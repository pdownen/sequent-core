module Language.SequentCore.Simpl.Env (
  SimplEnv(..), SimplIdSubst, SubstAns(..), IdDefEnv, Definition(..),

  InCommand, InValue, InFrame, InCont, InAlt, InBind,
  InId, InVar, InTyVar, InCoVar,
  OutCommand, OutValue, OutFrame, OutCont, OutAlt, OutBind,
  OutId, OutVar, OutTyVar, OutCoVar,
  
  initialEnv, mkSuspension, enterScope, enterScopes, uniqAway,
  substId, substTy, substCo, extendIdSubst,
  zapSubstEnvs, setSubstEnvs,
  suspendAndZapEnv, suspendAndSetEnv, restoreEnv
) where

import Language.SequentCore.Syntax

import BasicTypes ( TopLevelFlag(..) )
import Coercion   ( Coercion, CvSubstEnv, CvSubst, mkCvSubst )
import qualified Coercion
import CoreSyn    ( AltCon(..) )
import Id
import Outputable
import Type       ( Type, TvSubstEnv, TvSubst, mkTvSubst, tyVarsOfType )
import qualified Type
import Var
import VarEnv
import VarSet

import Data.Maybe

data SimplEnv
  = SimplEnv    { se_idSubst :: SimplIdSubst    -- InId    |--> SubstAns (in/out)
                , se_tvSubst :: TvSubstEnv      -- InTyVar |--> OutType
                , se_cvSubst :: CvSubstEnv      -- InCoVar |--> OutCoercion
                , se_cont    :: Maybe SuspCont
                , se_inScope :: InScopeSet      -- OutVar  |--> OutVar
                , se_defs    :: IdDefEnv }      -- OutId   |--> Definition (out)

type SimplIdSubst = IdEnv SubstAns -- InId |--> SubstAns
data SubstAns
  = DoneComm OutCommand
  | DoneId OutId
  | SuspComm SimplIdSubst TvSubstEnv CvSubstEnv InCommand

data SuspCont
  = SuspCont SimplIdSubst TvSubstEnv CvSubstEnv (Maybe SuspCont) InCont

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

mkSuspension :: SimplEnv -> InCommand -> SubstAns
mkSuspension env c
  = SuspComm (se_idSubst env) (se_tvSubst env) (se_cvSubst env) c

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
        , se_cvSubst = emptyVarEnv }

setSubstEnvs :: SimplEnv -> SimplIdSubst -> TvSubstEnv -> CvSubstEnv -> SimplEnv
setSubstEnvs env ids tvs cvs
  = env { se_idSubst = ids
        , se_tvSubst = tvs
        , se_cvSubst = cvs }

suspendAndZapEnv :: SimplEnv -> InCont -> SimplEnv
suspendAndZapEnv env
  = suspendAndSetEnv env emptyVarEnv emptyVarEnv emptyVarEnv

suspendAndSetEnv :: SimplEnv -> SimplIdSubst -> TvSubstEnv -> CvSubstEnv
                 -> InCont -> SimplEnv
suspendAndSetEnv env ids tvs cvs cont
  = env { se_idSubst = ids
        , se_tvSubst = tvs
        , se_cvSubst = cvs
        , se_cont    = Just (SuspCont (se_idSubst env)
                                      (se_tvSubst env)
                                      (se_cvSubst env)
                                      (se_cont env)
                                      cont) }

restoreEnv :: SimplEnv -> Maybe (SimplEnv, InCont)
restoreEnv env
  = se_cont env >>= \(SuspCont ids tvs cvs susp cont) ->
      return (env { se_idSubst = ids
                  , se_tvSubst = tvs
                  , se_cvSubst = cvs
                  , se_cont    = susp }, cont)
