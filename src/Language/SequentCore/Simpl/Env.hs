module Language.SequentCore.Simpl.Env (
  SimplEnv(..), StaticEnv, SimplIdSubst, SubstAns(..), IdDefEnv, Definition(..),

  InCommand, InValue, InFrame, InCont, InAlt, InBind,
  InId, InVar, InTyVar, InCoVar,
  OutCommand, OutValue, OutFrame, OutCont, OutAlt, OutBind,
  OutId, OutVar, OutTyVar, OutCoVar,
  
  initialEnv, mkSuspension, enterScope, enterScopes, uniqAway,
  substId, substTy, substTyStatic, substCo, substCoStatic, extendIdSubst,
  zapSubstEnvs, setSubstEnvs, staticPart, setStaticPart,
  suspendAndZapEnv, suspendAndSetEnv, zapCont, bindCont, restoreEnv
) where

import Language.SequentCore.Pretty ()
import Language.SequentCore.Syntax

import BasicTypes ( TopLevelFlag(..) )
import Coercion   ( Coercion, CvSubstEnv, CvSubst, mkCvSubst )
import qualified Coercion
import Id
import Outputable
import Type       ( Type, TvSubstEnv, TvSubst, mkTvSubst, tyVarsOfType )
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
                , se_defs    :: IdDefEnv }      -- OutId   |--> Definition (out)

newtype StaticEnv = StaticEnv SimplEnv -- Ignore se_inScope and se_defs

type SimplIdSubst = IdEnv SubstAns -- InId |--> SubstAns
data SubstAns
  = DoneComm OutCommand
  | DoneId OutId
  | SuspComm StaticEnv InCommand

data SuspCont
  = SuspCont StaticEnv InCont

-- The original simplifier uses the IdDetails stored in a Var to store unfolding
-- info. We store similar data externally instead. (This is based on the Secrets
-- paper, section 6.3.)
type IdDefEnv = IdEnv Definition
data Definition
  = BoundTo OutCommand TopLevelFlag
  | NotAmong [AltCon]

type InCommand  = SeqCoreCommand
type InValue    = SeqCoreValue
type InFrame    = SeqCoreFrame
type InCont     = SeqCoreCont
type InAlt      = SeqCoreAlt
type InBind     = SeqCoreBind
type InId       = Id
type InVar      = Var
type InTyVar    = TyVar
type InCoVar    = CoVar

type OutCommand = SeqCoreCommand
type OutValue   = SeqCoreValue
type OutFrame   = SeqCoreFrame
type OutCont    = SeqCoreCont
type OutAlt     = SeqCoreAlt
type OutBind    = SeqCoreBind
type OutId      = Id
type OutVar     = Var
type OutTyVar   = TyVar
type OutCoVar   = CoVar

initialEnv :: SimplEnv
initialEnv = SimplEnv { se_idSubst = emptyVarEnv
                      , se_tvSubst = emptyVarEnv
                      , se_cvSubst = emptyVarEnv
                      , se_cont    = Nothing
                      , se_inScope = emptyInScopeSet
                      , se_defs    = emptyVarEnv }

mkSuspension :: StaticEnv -> InCommand -> SubstAns
mkSuspension = SuspComm

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
      Nothing             -> DoneId (refine ins x)
      Just (DoneId x')    -> DoneId (refine ins x')
      Just (DoneComm c)    | Just (Var x') <- asValueCommand c
                          -> DoneId (refine ins x')
      Just ans            -> ans

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
  = suspendAndSetEnv env (StaticEnv initialEnv) cont

suspendAndSetEnv :: SimplEnv -> StaticEnv -> InCont -> SimplEnv
suspendAndSetEnv env (StaticEnv stat) cont
  = env { se_idSubst = se_idSubst stat
        , se_tvSubst = se_tvSubst stat
        , se_cvSubst = se_cvSubst stat
        , se_cont    = Just (SuspCont (StaticEnv env) cont) }

bindCont :: SimplEnv -> StaticEnv -> InCont -> SimplEnv
bindCont env stat cont
  = env { se_cont = Just (SuspCont stat cont) }

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
  ppr (SimplEnv ids tvs cvs cont in_scope _defs)
    =  text "<InScope =" <+> braces (fsep (map ppr (varEnvElts (getInScopeVars in_scope))))
--    $$ text " Defs      =" <+> ppr defs
    $$ text " IdSubst   =" <+> ppr ids
    $$ text " TvSubst   =" <+> ppr tvs
    $$ text " CvSubst   =" <+> ppr cvs
    $$ text " Cont      =" <+> ppr cont
     <> char '>'

instance Outputable StaticEnv where
  ppr (StaticEnv (SimplEnv ids tvs cvs cont _in_scope _defs))
    =  text "<IdSubst   =" <+> ppr ids
    $$ text " TvSubst   =" <+> ppr tvs
    $$ text " CvSubst   =" <+> ppr cvs
    $$ text " Cont      =" <+> ppr cont
     <> char '>'

instance Outputable SubstAns where
  ppr (DoneComm c) = brackets (text "Command:" <+> ppr c)
  ppr (DoneId x) = brackets (text "Id:" <+> ppr x)
  ppr (SuspComm env c)
    = brackets $ hang (text "Suspended:") 2 (sep [ppr env, ppr c])

instance Outputable SuspCont where
  ppr (SuspCont _env cont)
    = ppr cont

instance Outputable Definition where
  ppr (BoundTo c level) = brackets (ppr level) <+> ppr c
  ppr (NotAmong alts) = text "NotAmong" <+> ppr alts
