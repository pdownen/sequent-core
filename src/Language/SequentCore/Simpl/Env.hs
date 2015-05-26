module Language.SequentCore.Simpl.Env (
  SimplEnv(..), StaticEnv, SimplIdSubst, SubstAns(..), IdDefEnv, Definition(..),
  Guidance(..),

  InCommand, InValue, InCont, InAlt, InBind,
  InId, InVar, InTyVar, InCoVar,
  OutCommand, OutValue, OutCont, OutAlt, OutBind,
  OutId, OutVar, OutTyVar, OutCoVar,
  
  mkBoundTo,
  initialEnv, mkSuspension, enterScope, enterScopes, mkFreshVar, mkFreshContId,
  substId, substTy, substTyStatic, substCo, substCoStatic, extendIdSubst,
  zapSubstEnvs, setSubstEnvs, staticPart, setStaticPart,
  zapCont, bindCont, bindContAs, pushCont, setCont, restoreEnv,
  
  Floats, emptyFloats, addNonRecFloat, addRecFloats, zapFloats, mapFloats,
  extendFloats, addFloats, wrapFloats, isEmptyFloats, doFloatFromRhs,
  getFloatBinds, getFloats,
  
  valueIsHNF, commandIsHNF
) where

import Language.SequentCore.Pretty ()
import Language.SequentCore.Simpl.ExprSize
import Language.SequentCore.Syntax

import BasicTypes ( OccInfo(..), TopLevelFlag(..), RecFlag(..)
                  , isTopLevel, isNotTopLevel, isNonRec )
import Coercion   ( Coercion, CvSubstEnv, CvSubst, mkCvSubst )
import qualified Coercion
import DynFlags ( DynFlags, ufCreationThreshold )
import FastString ( FastString, fsLit )
import Id
import Maybes
import OrdList
import Outputable
import Type       ( Type, TvSubstEnv, TvSubst, mkTvSubst, tyVarsOfType )
import qualified Type
import UniqSupply
import Var
import VarEnv
import VarSet

import Control.Exception ( assert )

infixl 1 `setStaticPart`

data SimplEnv
  = SimplEnv    { se_idSubst :: SimplIdSubst    -- InId    |--> SubstAns (in/out)
                , se_tvSubst :: TvSubstEnv      -- InTyVar |--> OutType
                , se_cvSubst :: CvSubstEnv      -- InCoVar |--> OutCoercion
                , se_retId   :: Maybe ContId
                , se_inScope :: InScopeSet      -- OutVar  |--> OutVar
                , se_defs    :: IdDefEnv        -- OutId   |--> Definition (out)
                , se_floats  :: Floats
                , se_dflags  :: DynFlags }

newtype StaticEnv = StaticEnv SimplEnv -- Ignore se_inScope, se_floats, se_defs

type SimplIdSubst = IdEnv SubstAns -- InId |--> SubstAns
data SubstAns
  = DoneVal OutValue
  | DoneId OutId
  | SuspVal StaticEnv InValue

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
  = let cap = ufCreationThreshold dflags
    in case valueSize dflags cap val of
         Nothing -> Never
         Just (ExprSize base args res) ->
           Sometimes base args res

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
             , se_retId   = Nothing
             , se_inScope = emptyInScopeSet
             , se_defs    = emptyVarEnv
             , se_floats  = emptyFloats
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

mkFreshVar :: MonadUnique m => SimplEnv -> FastString -> Type -> m (SimplEnv, Var)
mkFreshVar env name ty
  = mkFresh env name ty (\x -> x)

mkFreshContId :: MonadUnique m => SimplEnv -> FastString -> Type -> m (SimplEnv, ContId)
mkFreshContId env name ty
  = mkFresh env name ty asContId
    
mkFresh :: MonadUnique m => SimplEnv -> FastString -> Type -> (Id -> Id)
                                     -> m (SimplEnv, Var)
mkFresh env name ty tag
  = do
    x <- mkSysLocalM name ty
    let x'   = uniqAway (se_inScope env) (tag x)
        env' = env { se_inScope = extendInScopeSet (se_inScope env) x' }
    return (env', x')

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
    vars = varEnvElts (getInScopeVars ins)

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
        , se_retId   = Nothing }

setSubstEnvs :: SimplEnv -> SimplIdSubst -> TvSubstEnv -> CvSubstEnv
             -> Maybe ContId -> SimplEnv
setSubstEnvs env ids tvs cvs k
  = env { se_idSubst = ids
        , se_tvSubst = tvs
        , se_cvSubst = cvs
        , se_retId   = k }

bindCont :: MonadUnique m => SimplEnv -> StaticEnv -> InCont -> m SimplEnv
bindCont env stat cont
  = do
    let retId = se_retId env `orElse` panic "bindCont at top level"
        retTy = Type.funArgTy (idType retId)
    k <- mkSysLocalM (fsLit "k") (Type.mkFunTy (contType cont) retTy)
    let k' = asContId $ uniqAway (se_inScope env) k
    return $ bindContAs env k' stat cont

bindContAs :: SimplEnv -> ContId -> StaticEnv -> InCont -> SimplEnv
bindContAs env k stat cont
  = env { se_inScope = extendInScopeSet (se_inScope env) k
        , se_idSubst = extendVarEnv (se_idSubst env) k
                         (SuspVal stat (Cont cont))
        , se_retId   = Just k }

pushCont :: MonadUnique m => SimplEnv -> InCont -> m SimplEnv
pushCont env cont
  = bindCont env (staticPart env) cont

zapCont :: SimplEnv -> SimplEnv
zapCont env = env { se_retId = Nothing }

setCont :: SimplEnv -> ContId -> SimplEnv
setCont env k = env { se_retId = Just k }

staticPart :: SimplEnv -> StaticEnv
staticPart = StaticEnv

setStaticPart :: SimplEnv -> StaticEnv -> SimplEnv
setStaticPart dest (StaticEnv src)
  = dest { se_idSubst = se_idSubst src
         , se_tvSubst = se_tvSubst src
         , se_cvSubst = se_cvSubst src
         , se_retId   = se_retId   src }

inScope :: StaticEnv -> SimplEnv -> SimplEnv
inScope = flip setStaticPart

restoreEnv :: SimplEnv -> Maybe (SimplEnv, InCont)
restoreEnv env
  = do
    k <- se_retId env
    substAns <- lookupVarEnv (se_idSubst env) k
    case substAns of
      DoneVal val -> use (zapSubstEnvs env, val)
      DoneId _ -> Nothing -- not sure what this means, but consistent with prev
      SuspVal env' val -> use (env' `inScope` env, val)
      where
        use (env', Cont cont) = Just (env', cont)
        use (_env', val) = pprPanic "restoreEnv" (ppr val)

-- See [Simplifier floats] in SimplEnv

data Floats = Floats (OrdList OutBind) FloatFlag

data FloatFlag
  = FltLifted   -- All bindings are lifted and lazy
                --  Hence ok to float to top level, or recursive

  | FltOkSpec   -- All bindings are FltLifted *or*
                --      strict (perhaps because unlifted,
                --      perhaps because of a strict binder),
                --        *and* ok-for-speculation
                --  Hence ok to float out of the RHS
                --  of a lazy non-recursive let binding
                --  (but not to top level, or into a rec group)

  | FltCareful  -- At least one binding is strict (or unlifted)
                --      and not guaranteed cheap
                --      Do not float these bindings out of a lazy let

andFF :: FloatFlag -> FloatFlag -> FloatFlag
andFF FltCareful _          = FltCareful
andFF FltOkSpec  FltCareful = FltCareful
andFF FltOkSpec  _          = FltOkSpec
andFF FltLifted  flt        = flt

classifyFF :: SeqCoreBind -> FloatFlag
classifyFF (Rec _) = FltLifted
classifyFF (NonRec bndr rhs)
  | not (isStrictId bndr)    = FltLifted
  | valueOkForSpeculation rhs = FltOkSpec
  | otherwise                = FltCareful

doFloatFromRhs :: TopLevelFlag -> RecFlag -> Bool -> OutValue -> SimplEnv -> Bool
-- If you change this function look also at FloatIn.noFloatFromRhs
doFloatFromRhs lvl rc str rhs (SimplEnv {se_floats = Floats fs ff})
  =  not (isNilOL fs) && want_to_float && can_float
  where
     want_to_float = isTopLevel lvl || valueIsCheap rhs || valueIsExpandable rhs 
                     -- See Note [Float when cheap or expandable]
     can_float = case ff of
                   FltLifted  -> True
                   FltOkSpec  -> isNotTopLevel lvl && isNonRec rc
                   FltCareful -> isNotTopLevel lvl && isNonRec rc && str

emptyFloats :: Floats
emptyFloats = Floats nilOL FltLifted

unitFloat :: OutBind -> Floats
unitFloat bind = Floats (unitOL bind) (classifyFF bind)

addNonRecFloat :: SimplEnv -> OutId -> OutValue -> SimplEnv
addNonRecFloat env id rhs
  = id `seq`   -- This seq forces the Id, and hence its IdInfo,
               -- and hence any inner substitutions
    env { se_floats = se_floats env `addFlts` unitFloat (NonRec id rhs),
          se_inScope = extendInScopeSet (se_inScope env) id }

mapFloats :: SimplEnv -> ((OutId, OutValue) -> (OutId, OutValue)) -> SimplEnv
mapFloats env@SimplEnv { se_floats = Floats fs ff } fun
   = env { se_floats = Floats (mapOL app fs) ff }
   where
     app (NonRec b e) = case fun (b,e) of (b',e') -> NonRec b' e'
     app (Rec bs)     = Rec (map fun bs)

extendFloats :: SimplEnv -> OutBind -> SimplEnv
-- Add these bindings to the floats, and extend the in-scope env too
extendFloats env bind
  = env { se_floats  = se_floats env `addFlts` unitFloat bind,
          se_inScope = extendInScopeSetList (se_inScope env) bndrs }
  where
    bndrs = bindersOf bind

addFloats :: SimplEnv -> SimplEnv -> SimplEnv
-- Add the floats for env2 to env1;
-- *plus* the in-scope set for env2, which is bigger
-- than that for env1
addFloats env1 env2
  = env1 {se_floats = se_floats env1 `addFlts` se_floats env2,
          se_inScope = se_inScope env2 }

wrapFloats :: SimplEnv -> OutCommand -> OutCommand
wrapFloats env cmd = foldrOL wrap cmd (floatBinds (se_floats env))
  where
    wrap :: OutBind -> OutCommand -> OutCommand
    wrap bind@(Rec {}) cmd = cmd { cmdLet = bind : cmdLet cmd }
    wrap (NonRec b r)  cmd = addNonRec b r cmd

addFlts :: Floats -> Floats -> Floats
addFlts (Floats bs1 l1) (Floats bs2 l2)
  = Floats (bs1 `appOL` bs2) (l1 `andFF` l2)

zapFloats :: SimplEnv -> SimplEnv
zapFloats env = env { se_floats = emptyFloats }

addRecFloats :: SimplEnv -> SimplEnv -> SimplEnv
-- Flattens the floats from env2 into a single Rec group,
-- prepends the floats from env1, and puts the result back in env2
-- This is all very specific to the way recursive bindings are
-- handled; see Simpl.simplRecBind
addRecFloats env1 env2@(SimplEnv {se_floats = Floats bs ff})
  = assert (case ff of { FltLifted -> True; _ -> False })
  $ env2 {se_floats = se_floats env1 `addFlts` unitFloat (Rec (flattenBinds (fromOL bs)))}

getFloatBinds :: Floats -> [OutBind]
getFloatBinds = fromOL . floatBinds

floatBinds :: Floats -> OrdList OutBind
floatBinds (Floats bs _) = bs

getFloats :: SimplEnv -> Floats
getFloats = se_floats

isEmptyFloats :: SimplEnv -> Bool
isEmptyFloats = isNilOL . floatBinds . se_floats

-- TODO This might be in Syntax, but since we're not storing our "unfoldings" in
-- ids, we rely on the environment to tell us whether a variable has been
-- evaluated.

valueIsHNF :: SimplEnv -> SeqCoreValue -> Bool
valueIsHNF _   (Lit {})  = True
valueIsHNF _   (Cons {}) = True
valueIsHNF env (Var id)
  = case lookupVarEnv (se_defs env) id of
      Just (NotAmong {})            -> True
      Just (BoundTo val _ _ _) -> valueIsHNF env val
      _                             -> False
valueIsHNF env (Compute _ comm) = commandIsHNF env comm
valueIsHNF _   _        = False

commandIsHNF :: SimplEnv -> SeqCoreCommand -> Bool
commandIsHNF _env (Command [] (Var fid) cont)
  | let (args, _) = collectArgs cont
  , length args < idArity fid
  = True
commandIsHNF _env (Command _ (Compute {}) _)
  = False
commandIsHNF env (Command [] val (Return _))
  = valueIsHNF env val
commandIsHNF _ _
  = False

instance Outputable SimplEnv where
  ppr (SimplEnv ids tvs cvs cont in_scope _defs floats _dflags)
    =  text "<InScope =" <+> braces (fsep (map ppr (varEnvElts (getInScopeVars in_scope))))
--    $$ text " Defs      =" <+> ppr defs
    $$ text " IdSubst   =" <+> ppr ids
    $$ text " TvSubst   =" <+> ppr tvs
    $$ text " CvSubst   =" <+> ppr cvs
    $$ text " Cont      =" <+> ppr cont
    $$ text " Floats    =" <+> ppr floats
     <> char '>'

instance Outputable StaticEnv where
  ppr (StaticEnv (SimplEnv ids tvs cvs cont _in_scope _defs _floats _dflags))
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

instance Outputable Definition where
  ppr (BoundTo c occ level guid)
    = brackets (ppr occ <+> comma <+> ppr level <+> ppr guid) <+> ppr c
  ppr (NotAmong alts) = text "NotAmong" <+> ppr alts

instance Outputable Guidance where
  ppr Never = text "Never"
  ppr (Sometimes base argDiscs resDisc)
    = text "Sometimes" <+> brackets (int base <+> ppr argDiscs <+> int resDisc)

instance Outputable Floats where
  ppr (Floats binds ff) = ppr ff $$ ppr (fromOL binds)

instance Outputable FloatFlag where
  ppr FltLifted = text "FltLifted"
  ppr FltOkSpec = text "FltOkSpec"
  ppr FltCareful = text "FltCareful"
