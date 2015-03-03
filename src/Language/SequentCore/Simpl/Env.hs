module Language.SequentCore.Simpl.Env (
  SimplEnv(..), StaticEnv, SimplIdSubst, SubstAns(..), IdDefEnv, Definition(..),
  Guidance(..),

  InCommand, InValue, InCont, InAlt, InBind,
  InId, InVar, InTyVar, InCoVar,
  OutCommand, OutValue, OutCont, OutAlt, OutBind,
  OutId, OutVar, OutTyVar, OutCoVar,
  
  mkBoundTo,
  initialEnv, mkSuspension, enterScope, enterScopes, uniqAway,
  substId, substTy, substTyStatic, substCo, substCoStatic, extendIdSubst,
  zapSubstEnvs, setSubstEnvs, staticPart, setStaticPart,
  suspendAndZapEnv, suspendAndSetEnv, zapCont, bindCont, pushCont, restoreEnv
) where

import Language.SequentCore.Pretty ()
import Language.SequentCore.Simpl.ExprSize
import Language.SequentCore.Syntax

import BasicTypes ( OccInfo(..), TopLevelFlag(..) )
import Bag        ( Bag, foldlBag )
import Coercion   ( Coercion, CvSubstEnv, CvSubst, mkCvSubst )
import qualified Coercion
import DynFlags ( DynFlags, ufCreationThreshold )
import Id
import Outputable
import Type       ( Type, TvSubstEnv, TvSubst, mkTvSubst, tyVarsOfType, isFunTy )
import qualified Type
import Var
import VarEnv
import VarSet

import Data.Maybe

infixl 1 `setStaticPart`

data SimplEnv
  = SimplEnv    { se_idSubst :: SimplIdSubst    -- InId    |--> SubstAns (in/out)
                , se_tvSubst :: TvSubstEnv      -- InTyVar |--> OutType
                , se_cvSubst :: CvSubstEnv      -- InCoVar |--> OutCoercion
                , se_cont    :: Maybe SuspCont
                , se_inScope :: InScopeSet      -- OutVar  |--> OutVar
                , se_defs    :: IdDefEnv        -- OutId   |--> Definition (out)
                , se_dflags  :: DynFlags }

newtype StaticEnv = StaticEnv SimplEnv -- Ignore se_inScope and se_defs

type SimplIdSubst = IdEnv SubstAns -- InId |--> SubstAns
data SubstAns
  = DoneVal OutValue
  | DoneId OutId
  | SuspVal StaticEnv InValue

data SuspCont
  = SuspCont StaticEnv InCont

-- The original simplifier uses the IdDetails stored in a Var to store unfolding
-- info. We store similar data externally instead. (This is based on the Secrets
-- paper, section 6.3.)
type IdDefEnv = IdEnv Definition
data Definition
  = BoundTo OutValue OccInfo TopLevelFlag Guidance
  | NotAmong [AltCon]

data Guidance
  = Never
-- TODO: Usually  { guEvenIfUnsat :: Bool, guEvenIfBoring :: Bool }
  | Sometimes { guSize :: Int
              , guArgDiscounts :: [Int]
              , guResultDiscount :: Int }

mkBoundTo :: DynFlags -> OutValue -> OccInfo -> TopLevelFlag -> Definition
mkBoundTo dflags val occ level = BoundTo val occ level (mkGuidance dflags val)

mkGuidance :: DynFlags -> OutValue -> Guidance
mkGuidance dflags val
  = let (xs, body) = collectLambdas val
        cap        = ufCreationThreshold dflags
        valBinders = filter isId xs

        discount :: Bag (Id, Int) -> Id -> Int
        discount cbs bndr = foldlBag combine 0 cbs
           where
             combine acc (bndr', disc) 
               | bndr == bndr' = acc `plus_disc` disc
               | otherwise     = acc
   
             plus_disc :: Int -> Int -> Int
             plus_disc | isFunTy (idType bndr) = max
                       | otherwise             = (+)
    in case commandSize dflags cap valBinders body of
         TooBig -> Never
         ExprSize base cased disc ->
           Sometimes base (map (discount cased) valBinders) disc

type InCommand  = SeqCoreCommand
type InValue    = SeqCoreValue
type InCont     = SeqCoreCont
type InAlt      = SeqCoreAlt
type InBind     = SeqCoreBind
type InId       = Id
type InVar      = Var
type InTyVar    = TyVar
type InCoVar    = CoVar

type OutCommand = SeqCoreCommand
type OutValue   = SeqCoreValue
type OutCont    = SeqCoreCont
type OutAlt     = SeqCoreAlt
type OutBind    = SeqCoreBind
type OutId      = Id
type OutVar     = Var
type OutTyVar   = TyVar
type OutCoVar   = CoVar

initialEnv :: DynFlags -> SimplEnv
initialEnv dflags
  = SimplEnv { se_idSubst = emptyVarEnv
             , se_tvSubst = emptyVarEnv
             , se_cvSubst = emptyVarEnv
             , se_cont    = Nothing
             , se_inScope = emptyInScopeSet
             , se_defs    = emptyVarEnv
             , se_dflags  = dflags }

mkSuspension :: StaticEnv -> InValue -> SubstAns
mkSuspension = SuspVal

enterScope :: SimplEnv -> InVar -> (SimplEnv, OutVar)
enterScope env x
  = (env'', x')
  where
    SimplEnv { se_inScope = ins, se_idSubst = ids } = env
    x1    = uniqAway ins x
    x'    = substIdType env x1
    env'  | x' /= x   = env { se_idSubst = extendVarEnv ids x (DoneId x') }
          | otherwise = env
    ins'  = extendInScopeSet ins x'
    env'' = env' { se_inScope = ins' }

enterScopes :: SimplEnv -> [InVar] -> (SimplEnv, [OutVar])
enterScopes env []
  = (env, [])
enterScopes env (x : xs)
  = (env'', x' : xs')
  where
    (env', x') = enterScope env x
    (env'', xs') = enterScopes env' xs

substId :: SimplEnv -> InId -> SubstAns
substId (SimplEnv { se_idSubst = ids, se_inScope = ins }) x
  = case lookupVarEnv ids x of
      -- See comments in GHC's SimplEnv.substId for explanations
      Nothing                 -> DoneId (refine ins x)
      Just (DoneId x')        -> DoneId (refine ins x')
      Just (DoneVal (Var x')) -> DoneId (refine ins x')
      Just ans                -> ans

refine :: InScopeSet -> OutVar -> OutVar
refine ins x
  | isLocalId x
  = case lookupInScope ins x of
      Just x' -> x'
      Nothing -> pprTrace "refine" (text "variable not in scope:" <+> ppr x) x
  | otherwise
  = x

getTvSubst :: SimplEnv -> TvSubst
getTvSubst env = mkTvSubst (se_inScope env) (se_tvSubst env)

substTy :: SimplEnv -> Type -> Type
substTy env t = Type.substTy (getTvSubst env) t

substTyStatic :: StaticEnv -> Type -> Type
substTyStatic (StaticEnv env) = substTy env

substIdType :: SimplEnv -> Var -> Var
substIdType env x
  | isEmptyVarEnv tvs || isEmptyVarSet (tyVarsOfType ty)
  = x
  | otherwise
  = x `setIdType` substTy env ty
  where
    tvs = se_tvSubst env
    ty = idType x

getCvSubst :: SimplEnv -> CvSubst
getCvSubst env = mkCvSubstFromSubstEnv (se_inScope env) (se_cvSubst env)

substCo :: SimplEnv -> Coercion -> Coercion
substCo env co = Coercion.substCo (getCvSubst env) co

substCoStatic :: StaticEnv -> Coercion -> Coercion
substCoStatic (StaticEnv env) = substCo env

cvSubstPairs :: InScopeSet -> CvSubstEnv -> [(Var, Coercion)]
cvSubstPairs ins cvs
  = mapMaybe lookupWithKey vars
  where
    lookupWithKey x = lookupVarEnv cvs x >>= \co -> Just (x, co)
    vars = (varEnvElts (getInScopeVars ins))

mkCvSubstFromSubstEnv :: InScopeSet -> CvSubstEnv -> CvSubst
mkCvSubstFromSubstEnv ins cvs = mkCvSubst ins (cvSubstPairs ins cvs)

extendIdSubst :: SimplEnv -> InVar -> SubstAns -> SimplEnv
extendIdSubst env x rhs
  = env { se_idSubst = extendVarEnv (se_idSubst env) x rhs }

zapSubstEnvs :: SimplEnv -> SimplEnv
zapSubstEnvs env
  = env { se_idSubst = emptyVarEnv
        , se_tvSubst = emptyVarEnv
        , se_cvSubst = emptyVarEnv
        , se_cont    = Nothing }

setSubstEnvs :: SimplEnv -> SimplIdSubst -> TvSubstEnv -> CvSubstEnv
             -> Maybe SuspCont -> SimplEnv
setSubstEnvs env ids tvs cvs k
  = env { se_idSubst = ids
        , se_tvSubst = tvs
        , se_cvSubst = cvs
        , se_cont    = k }

suspendAndZapEnv :: SimplEnv -> InCont -> SimplEnv
suspendAndZapEnv env cont
  = suspendAndSetEnv env (StaticEnv (initialEnv (se_dflags env))) cont

suspendAndSetEnv :: SimplEnv -> StaticEnv -> InCont -> SimplEnv
suspendAndSetEnv env (StaticEnv stat) cont
  = env { se_idSubst = se_idSubst stat
        , se_tvSubst = se_tvSubst stat
        , se_cvSubst = se_cvSubst stat
        , se_cont    = Just (SuspCont (StaticEnv env) cont) }

bindCont :: SimplEnv -> StaticEnv -> InCont -> SimplEnv
bindCont env stat cont
  = env { se_cont = Just (SuspCont stat cont) }

pushCont :: SimplEnv -> InCont -> SimplEnv
pushCont env cont
  = bindCont env (staticPart env) cont

zapCont :: SimplEnv -> SimplEnv
zapCont env = env { se_cont = Nothing }

staticPart :: SimplEnv -> StaticEnv
staticPart = StaticEnv

setStaticPart :: SimplEnv -> StaticEnv -> SimplEnv
setStaticPart dest (StaticEnv src)
  = dest { se_idSubst = se_idSubst src
         , se_tvSubst = se_tvSubst src
         , se_cvSubst = se_cvSubst src
         , se_cont    = se_cont    src }

restoreEnv :: SimplEnv -> Maybe (SimplEnv, InCont)
restoreEnv env
  = se_cont env >>= \(SuspCont env' cont) ->
      return (env `setStaticPart` env', cont)

instance Outputable SimplEnv where
  ppr (SimplEnv ids tvs cvs cont in_scope _defs _dflags)
    =  text "<InScope =" <+> braces (fsep (map ppr (varEnvElts (getInScopeVars in_scope))))
--    $$ text " Defs      =" <+> ppr defs
    $$ text " IdSubst   =" <+> ppr ids
    $$ text " TvSubst   =" <+> ppr tvs
    $$ text " CvSubst   =" <+> ppr cvs
    $$ text " Cont      =" <+> ppr cont
     <> char '>'

instance Outputable StaticEnv where
  ppr (StaticEnv (SimplEnv ids tvs cvs cont _in_scope _defs _dflags))
    =  text "<IdSubst   =" <+> ppr ids
    $$ text " TvSubst   =" <+> ppr tvs
    $$ text " CvSubst   =" <+> ppr cvs
    $$ text " Cont      =" <+> ppr cont
     <> char '>'

instance Outputable SubstAns where
  ppr (DoneVal v) = brackets (text "Value:" <+> ppr v)
  ppr (DoneId x) = brackets (text "Id:" <+> ppr x)
  ppr (SuspVal env v)
    = brackets $ hang (text "Suspended:") 2 (sep [ppr env, ppr v])

instance Outputable SuspCont where
  ppr (SuspCont _env cont)
    = ppr cont

instance Outputable Definition where
  ppr (BoundTo c occ level guid)
    = brackets (ppr occ <+> comma <+> ppr level <+> ppr guid) <+> ppr c
  ppr (NotAmong alts) = text "NotAmong" <+> ppr alts

instance Outputable Guidance where
  ppr Never = text "Never"
  ppr (Sometimes base argDiscs resDisc)
    = text "Sometimes" <+> brackets (int base <+> ppr argDiscs <+> int resDisc)
