{-# LANGUAGE ParallelListComp, TupleSections, MultiWayIf #-}

-- | 
-- Module      : Language.SequentCore.Translate
-- Description : Core \<-\> Sequent Core
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Translation between Sequent Core and native GHC Core.

module Language.SequentCore.Translate (
  -- $txn
  fromCoreModule, termFromCoreExpr,
  bindsToCore,
  commandToCoreExpr, termToCoreExpr, CoreContext, kontToCoreExpr,
  onCoreExpr, onSequentCoreTerm
) where

import Language.SequentCore.Syntax
import Language.SequentCore.WiredIn

import BasicTypes ( Arity, RecFlag(..), TopLevelFlag(..), TupleSort(..)
                  , isNonRec, isNotTopLevel )
import CoreSubst
import qualified CoreSyn as Core
import qualified CoreUtils as Core
import qualified CoreFVs as Core
import FastString
import Id
import Maybes
import qualified MkCore as Core
import MkId
import qualified Outputable as Out
import Outputable  hiding ( (<>) )
import Type        hiding ( substTy )
import TysPrim
import TysWiredIn
import UniqFM     ( intersectUFM_C )
import Unique
import VarEnv
import VarSet

import Control.Applicative
import Control.Exception ( assert )
import Control.Monad
import Control.Monad.Fix
import Data.List
import Data.Monoid

-- $txn
-- The translations to and from Sequent Core are /not/ guaranteed to be perfect
-- inverses. However, any differences between @e@ and @commandToCoreExpr
-- (fromCoreExpr e)@ should be operationally insignificant, such as a @let@
-- floating out from a function being applied. A more precise characterization
-- of the indended invariants of these functions would entail some sort of
-- /bisimulation/, but it should suffice to know that the translations are
-- "faithful enough."

------------------------------------------------
-- Public interface for Core --> Sequent Core --
------------------------------------------------

-- | Translates a list of Core bindings into Sequent Core.
fromCoreModule :: [Core.CoreBind] -> [SeqCoreBind]
fromCoreModule = fromCoreBinds . escAnalProgram

-- | Translates a single Core expression as a Sequent Core term.
termFromCoreExpr :: Core.CoreExpr -> SeqCoreTerm
termFromCoreExpr expr
  = fromCoreExprAsTerm env markedExpr mkLetKontId
  where
    markedExpr = runEscM (escAnalExpr expr)
    env = initFromCoreEnv { fce_subst = freeVarSet }
    freeVarSet = mkSubst (mkInScopeSet (Core.exprFreeVars expr))
                   emptyVarEnv emptyVarEnv emptyVarEnv

---------------------------------------
-- Phase 1: Escape-analyse Core code --
---------------------------------------

{-
Note [Escape analysis]
~~~~~~~~~~~~~~~~~~~~~~

The purpose of the escape analysis is to work out which let-bound functions we
can translate as parameterized continuations rather than as functions. To do
this, we gather information on all the identifier's occurrences, namely:

  Does every occurrence of f appear in a non-escaping context?

To be in a non-escaping context, the occurrence of f must be a tail call in the
context that declared it - that is, not inside a lambda, an argument, a cast
(see Note [Calls inside casts]), etc.

We perform the escape analysis by passing a Var -> Bool mapping bottom-up. Any
candidate for contification (that is, any let-bound variable) that appears in an
expression will appear in the returned mapping. If f appears only in
non-escaping contexts (that is, does not escape), it maps to True; if it appears
at least once in an escaping context, it maps to False. When combining mappings,
say when analysing the branches of a case, we union them together, performing an
AND on any two variables that appear in both mappings. Then, whenever the
traversal returns from an escaping context, such as a lambda or an argument
position, we take the whole mapping and set every value to False, since every
variable that appears in such a context escapes.

(In practice, we save some time by keeping two sets rather than one mapping--one
records all variables seen, and the other records the subset of those that
escape. Rather than set every value to False, then, we just set the escapee set
equal to the occurrence set.)

The result of the escape analysis is an annotated version of the code where each
binder is marked according to whether it should be contified and, if so, what
its total arity is (that is, arity counting both type and value binders).

Note [Calls inside casts]
~~~~~~~~~~~~~~~~~~~~~~~~~

If we try to contify a function that's invoked inside a cast, the resulting
program will be ill-typed. From the perspective of (Dual) System FC's
operational semantics, this is unsurprising because a cast is an operation and
a tail call is definitionally the final operation a function performs. However,
the cast is a fiction; all casts (and types) are erased on translation to STG.
Hence CoreToStg's escape analysis is able to contify (or let-no-escape) more
functions than ours. It's unclear what the workaround might be, though it's also
unclear how often this is a problem in practice.
-}

-- Bottom-up data --

data EscapeAnalysis
  = EA { ea_nonEsc  :: IdEnv (TotalArity, Call)
       , ea_allVars :: IdSet }

type TotalArity = Arity -- Counts *all* arguments, including types
type Call = [Core.CoreExpr]
data Occs = Esc | NonEsc TotalArity Call -- ^ Invariant: The call has the given
                                         -- length

emptyEscapeAnalysis :: EscapeAnalysis
emptyEscapeAnalysis = EA { ea_nonEsc  = emptyVarEnv
                         , ea_allVars = emptyVarSet }

unitCall :: Id -> Call -> EscapeAnalysis
unitCall x call = EA { ea_nonEsc  = unitVarEnv x (length call, call)
                     , ea_allVars = unitVarSet x }

markAllAsEscaping :: EscapeAnalysis -> EscapeAnalysis
markAllAsEscaping ea = ea { ea_nonEsc = emptyVarEnv }

-- XXX This implementation is probably slower than is possible using something
-- like Data.IntMap.mergeWithKey.
intersectWithMaybeVarEnv :: (elt1 -> elt2 -> Maybe elt3)
                         -> VarEnv elt1 -> VarEnv elt2 -> VarEnv elt3
intersectWithMaybeVarEnv f env1 env2
  = mapVarEnv fromJust $ filterVarEnv isJust $ intersectUFM_C f env1 env2

combineEscapeAnalyses :: EscapeAnalysis -> EscapeAnalysis -> EscapeAnalysis
combineEscapeAnalyses ea1 ea2
  | isEmptyVarEnv (ea_allVars ea1) = ea2
  | isEmptyVarEnv (ea_allVars ea2) = ea1
  | otherwise = EA { ea_allVars = ea_allVars ea1 `unionVarSet` ea_allVars ea2
                   , ea_nonEsc  = onlyIn1 `plusVarEnv` onlyIn2
                                          `plusVarEnv` nonEscBoth }
  where
    -- There are three ways a variable makes it into the non-escaping set for
    -- the combined analysis:
    --   1. It appears in the left non-escaping set and not at all on the right
    --   2. It appears in the right non-escaping set and not at all on the left
    --   3. It appears in both non-escaping sets with the same arity
    
    onlyIn1 = ea_nonEsc ea1 `minusVarEnv` ea_allVars ea2
    onlyIn2 = ea_nonEsc ea2 `minusVarEnv` ea_allVars ea1
    nonEscBoth = intersectWithMaybeVarEnv combine (ea_nonEsc ea1) (ea_nonEsc ea2)
    
    -- Only need to keep one call made to each function
    combine (n1, c1) (n2, _) | n1 == n2  = Just (n1, c1)
                             | otherwise = Nothing

forgetVars :: EscapeAnalysis -> [Id] -> EscapeAnalysis
forgetVars (EA { ea_nonEsc = nonEsc, ea_allVars = allVars }) xs
  = EA { ea_nonEsc  = nonEsc  `delVarEnvList` xs
       , ea_allVars = allVars `delVarSetList` xs }

occurrences :: EscapeAnalysis -> Id -> Maybe Occs
occurrences ea x
  | Just (n, cs) <- lookupVarEnv (ea_nonEsc ea) x = Just (NonEsc n cs)
  | x `elemVarEnv` ea_allVars ea                  = Just Esc
  | otherwise                                     = Nothing

-- If none of the variables escape, return the list of variables that occur
-- along with their apparent arities and call lists
allOccurrences :: EscapeAnalysis -> [Id] -> Maybe [(Id, Maybe (Int, Call))]
allOccurrences _  []       = Just []
allOccurrences ea (x : xs) = case occurrences ea x of
                               Just (NonEsc n call) -> ((x, Just (n, call)) :) <$>
                                                       allOccurrences ea xs
                               Just Esc             -> Nothing
                               Nothing              -> ((x, Nothing) :) <$>
                                                       allOccurrences ea xs

instance Monoid EscapeAnalysis where
  mempty = emptyEscapeAnalysis
  mappend = combineEscapeAnalyses

-- Top-down data --

type CandidateEnv = IdSet

emptyCandidateEnv :: CandidateEnv
emptyCandidateEnv = emptyVarSet

plusCandidate :: CandidateEnv -> Id -> CandidateEnv
plusCandidate = extendVarSet

plusCandidates :: CandidateEnv -> [Id] -> CandidateEnv
plusCandidates = extendVarSetList

isCandidateIn :: Id -> CandidateEnv -> Bool
isCandidateIn = elemVarSet

-- Monad --

-- | The monad underlying the escape analysis.
newtype EscM a = EscM { unEscM :: CandidateEnv -> (EscapeAnalysis, a) }

instance Monad EscM where
  return x = EscM $ \_   -> (emptyEscapeAnalysis, x)
  m >>= k  = EscM $ \env -> let (escs1, x) = unEscM m env
                                (escs2, y) = unEscM (k x) env
                                escs       = escs1 <> escs2
                            in (escs, y)

instance Functor EscM where fmap = liftM
instance Applicative EscM where { pure = return; (<*>) = ap }

instance MonadFix EscM where
  mfix f = EscM $ \env -> let pair@(_, ans) = unEscM (f ans) env
                          in pair

runEscM :: EscM a -> a
runEscM m = snd $ unEscM m emptyCandidateEnv

-- Monad operations --

getCandidates :: EscM CandidateEnv
getCandidates = EscM $ \env -> (emptyEscapeAnalysis, env)

alteringEnv :: (CandidateEnv -> CandidateEnv) -> EscM a -> EscM a
alteringEnv f m = EscM $ \env -> unEscM m (f env)

withEnv :: CandidateEnv -> EscM a -> EscM a
withEnv env m = EscM $ \_ -> unEscM m env

withoutCandidate :: Id -> EscM a -> EscM a
withoutCandidate x = alteringEnv (`delVarEnv` x)

withoutCandidates :: [Id] -> EscM a -> EscM a
withoutCandidates xs = alteringEnv (`delVarEnvList` xs)

reportCall :: Id -> Call -> EscM ()
reportCall x call = writeAnalysis (unitCall x call)

captureAnalysis, readAnalysis :: EscM a -> EscM (EscapeAnalysis, a)
captureAnalysis m = EscM $ \env -> let (escs, ans) = unEscM m env
                                   in (emptyEscapeAnalysis, (escs, ans))
readAnalysis m    = EscM $ \env -> let (escs, ans) = unEscM m env
                                   in (escs, (escs, ans))

writeAnalysis :: EscapeAnalysis -> EscM ()
writeAnalysis escs = EscM $ \_ -> (escs, ())

filterAnalysis :: (EscapeAnalysis -> EscapeAnalysis) -> EscM a -> EscM a
filterAnalysis f m = EscM $ \env -> let (escs, ans) = unEscM m env
                                    in (f escs, ans)

-- Result: Marked binders --

data KontOrFunc = MakeKont [ArgDesc] | MakeFunc
data ArgDesc    = FixedType Type | FixedVoidArg | TyArg TyVar | ValArg Type
data MarkedVar  = Marked Var KontOrFunc

unmark :: MarkedVar -> Var
unmark (Marked var _) = var

markVar :: Id -> Core.CoreExpr -> TotalArity -> Call -> MarkedVar
markVar x rhs arity call
  = Marked x ans
  where
    (bndrs, _body) = Core.collectBinders rhs
    realArity      = length bndrs
    
    ans | arity < realArity = MakeFunc
        | otherwise         = MakeKont (mkArgDescs (idType x) arity call)

-- | Return a constant value for each argument that needs one, given the type
-- and total arity of a function to be contified and a call made to it. Any
-- type parameters binding variables appearing in the return type must be made
-- constant, since the contified function will return to a fixed continuation in
-- which those parameters are not bound.
--
-- It's possible the total arity is greater than the number of arrows and foralls
-- in the type, but only if the return type of the function is a type variable
-- bound in an outer scope. This is fine, because the extra arguments cannot
-- change the actual return type, so we don't need to fix (mask out) the extra
-- arguments. TODO Be more sure about this.
mkArgDescs :: Type -> TotalArity -> Call -> [ArgDesc]
mkArgDescs ty arity call
  = go ty call
  where
    (_tyVars, retTy) = splitPiTyN ty arity
    freeInRetTy     = tyVarsOfType retTy
    
    go ty (Core.Type tyArg : call)
      | tyVar `elemVarSet` freeInRetTy
      = FixedType tyArg : mkArgDescs (substTyWith [tyVar] [tyArg] bodyTy)
                                     (length call) call -- start over with
                                                        -- new return type
      | otherwise
      = TyArg tyVar : go bodyTy call
      where
        (tyVar, bodyTy) = splitForAllTy_maybe ty `orElse`
                            pprPanic "mkArgDescs" (ppr ty <+> ppr tyArg)
    go ty (arg : call)
      | argTy `eqType` voidPrimTy
      = FixedVoidArg : go retTy call
      | otherwise
      = ValArg argTy : go retTy call
      where
        (argTy, retTy) = splitFunTy_maybe ty `orElse`
                           pprPanic "mkArgDescs" (ppr ty <+> ppr arg)
                           
    go _ _ = []
    
splitPiTyN :: Type -> TotalArity -> ([Maybe TyVar], Type)
splitPiTyN ty n
  | Just (tyVar, ty') <- splitForAllTy_maybe ty
  = let (args, retTy) = splitPiTyN ty' (n-1)
    in (Just tyVar : args, retTy)
  | Just (_, ty') <- splitFunTy_maybe ty
  = let (args, retTy) = splitPiTyN ty' (n-1)
    in (Nothing : args, retTy)
  | otherwise
  = ([], ty)

-- Escape analysis --

escAnalProgram :: Core.CoreProgram -> [Core.Bind MarkedVar]
escAnalProgram binds = runEscM (go binds)
  where
    go :: [Core.CoreBind] -> EscM [Core.Bind MarkedVar]
    go (bind:binds)
      = do
        (_escs, bind', binds') <- mfix $ \ ~(rec_escs_body, _, _) -> do
          (env', bind') <- escAnalBind TopLevel bind rec_escs_body
          (escs_body, binds') <- readAnalysis $ withEnv env' $ go binds
          return (escs_body, bind', binds')
        return (bind':binds')
    go [] = return []

escAnalBind :: TopLevelFlag -> Core.CoreBind -> EscapeAnalysis
            -> EscM (CandidateEnv, Core.Bind MarkedVar)
escAnalBind lvl (Core.NonRec bndr rhs) escs_body
  = do
    (escs_rhs, rhs') <- captureAnalysis $ escAnalRhs rhs
    let (marked, escs_rhs')
          | isNotTopLevel lvl
          , Just (NonEsc arity call) <- occurrences escs_body bndr
          = (markVar bndr rhs arity call, escs_rhs)
          | otherwise
          = (Marked bndr MakeFunc, markAllAsEscaping escs_rhs)
    writeAnalysis escs_rhs'
    escAnalId bndr
    
    env <- getCandidates
    return (env `plusCandidate` bndr, Core.NonRec marked rhs')

escAnalBind lvl (Core.Rec pairs) escs_body
  = do
    env <- getCandidates
    let (bndrs, rhss) = unzip pairs
        env' = env `plusCandidates` bndrs
    (escs_rhss, rhss') <- captureAnalysis $ withEnv env' $ do
                            mapM_ escAnalId bndrs
                            mapM escAnalRhs rhss
    let escs = escs_rhss <> escs_body
        occsList_maybe = allOccurrences escs bndrs
        kontify = isNotTopLevel lvl && isJust occsList_maybe
        pairs' | isNotTopLevel lvl
               , Just occsList <- occsList_maybe
               = [ (markVar bndr rhs arity calls, rhs')
                 | ((bndr, Just (arity, calls)), rhs, rhs') <-
                     zip3 occsList rhss rhss']
               | otherwise
               = [ (Marked bndr MakeFunc, rhs')
                 | (bndr, rhs') <- zip bndrs rhss']
        escs_rhss' | not kontify = markAllAsEscaping escs_rhss
                   | otherwise   = escs_rhss
    writeAnalysis (escs_rhss' `forgetVars` bndrs)
    return (env', Core.Rec pairs')

-- | Analyse an expression, but ignore its top-level lambdas
escAnalRhs :: Core.CoreExpr -> EscM (Core.Expr MarkedVar)
escAnalRhs expr
  = do
    let (bndrs, body) = Core.collectBinders expr
    body' <- withoutCandidates bndrs $ escAnalExpr body
    return $ Core.mkLams [ Marked bndr MakeFunc | bndr <- bndrs ] body'

escAnalExpr :: Core.CoreExpr -> EscM (Core.Expr MarkedVar)
escAnalExpr (Core.Var x)
  = escAnalApp x []
escAnalExpr (Core.Lit lit)
  = return $ Core.Lit lit
escAnalExpr expr@(Core.App {})
  = let (func, args) = Core.collectArgs expr
    in case func of
      Core.Var fid -> escAnalApp fid args
      _ -> filterAnalysis markAllAsEscaping $ do
             func' <- escAnalExpr func
             args' <- mapM escAnalExpr args
             return $ Core.mkApps func' args'
escAnalExpr expr@(Core.Lam {})
  = do
    let (tyBndrs, valBndrs, body) = Core.collectTyAndValBinders expr
    -- Remove value binders from the environment in case of shadowing - we
    -- won't report them as free vars
    body' <- withoutCandidates valBndrs $
             -- Lambdas ruin contification, so pretend the free vars escape
             filterAnalysis markAllAsEscaping $
             escAnalExpr body
    let bndrs' = [ Marked bndr MakeFunc | bndr <- tyBndrs ++ valBndrs ]
    return $ Core.mkLams bndrs' body'
escAnalExpr (Core.Let bind body)
  = do
    (_escs, bind', body') <- mfix $ \ ~(rec_escs_body, _, _) -> do
      (env', bind') <- escAnalBind NotTopLevel bind rec_escs_body
      (escs_body, body') <- readAnalysis $ withEnv env' $ escAnalExpr body
      return (escs_body, bind', body')
    return $ Core.Let bind' body'
escAnalExpr (Core.Case scrut bndr ty alts)
  = do
    scrut' <- filterAnalysis markAllAsEscaping $ escAnalExpr scrut
    alts' <- withoutCandidate bndr $ forM alts $ \(con, bndrs, rhs) -> do
      rhs' <- withoutCandidates bndrs $ escAnalExpr rhs
      return (con, map (`Marked` MakeFunc) bndrs, rhs')
    return $ Core.Case scrut' (Marked bndr MakeFunc) ty alts'
escAnalExpr (Core.Cast expr co)
  -- A call under a cast isn't a tail call, so pretend the free vars escape
  = (`Core.Cast` co) <$> filterAnalysis markAllAsEscaping (escAnalExpr expr)
escAnalExpr (Core.Tick ti expr)
  = Core.Tick ti <$> escAnalExpr expr
escAnalExpr (Core.Type ty)
  = return $ Core.Type ty
escAnalExpr (Core.Coercion co)
  = return $ Core.Coercion co

escAnalApp :: Id -> [Core.CoreExpr] -> EscM (Core.Expr MarkedVar)
escAnalApp fid args
  = do
    env <- getCandidates
    when (fid `isCandidateIn` env) $ reportCall fid args
    args' <- filterAnalysis markAllAsEscaping $ mapM escAnalExpr args
    return $ Core.mkApps (Core.Var fid) args'

-- Analyse unfolding and rules
escAnalId :: Id -> EscM ()
escAnalId x
  | isId x
  = do
    mapM_ escAnalRule (idCoreRules x)
    escAnalUnfolding (idUnfolding x)
  | otherwise
  = return ()

escAnalRule :: Core.CoreRule -> EscM ()
escAnalRule (Core.Rule { Core.ru_bndrs = bndrs, Core.ru_rhs = rhs })
  = void $ withoutCandidates bndrs $ escAnalExpr rhs
escAnalRule _
  = return ()

escAnalUnfolding :: Core.Unfolding -> EscM ()
escAnalUnfolding (Core.CoreUnfolding { Core.uf_tmpl = rhs  }) = void $ escAnalExpr rhs
escAnalUnfolding (Core.DFunUnfolding { Core.df_args = args }) = mapM_ escAnalExpr args
escAnalUnfolding _                                            = return ()

----------------------------------------
-- Phase 2: Translate to Sequent Core --
----------------------------------------

-- Continuation calling conventions --

-- | The protocol for invoking a given let-bound continuation. Currently all
-- such continuations must be invoked using a jump, so 'ByJump' is the only
-- constructor, but we must still keep track of which arguments are fixed and
-- should be omitted when converting a function call.
newtype KontCallConv = ByJump [ArgDesc]

-- Auxiliary datatype for idToKontId
data KontType = KTExists TyVar KontType | KTTuple [KontType] | KTType Type

-- | Convert an id to the id of a parameterized continuation, changing its type
-- according to the given calling convention.
idToPKontId :: Id -> KontCallConv -> PKontId
idToPKontId p (ByJump fixed)
  = p `setIdType` kontTypeToType (go (idType p) fixed)
  where
    go _  [] = KTTuple []
    go ty (FixedType tyArg : fixed')
      | Just (tyVar, ty') <- splitForAllTy_maybe ty
      = go (substTyWith [tyVar] [tyArg] ty') fixed'
    go ty (FixedVoidArg : fixed')
      | Just (argTy, retTy) <- splitFunTy_maybe ty
      = assert (argTy `eqType` voidPrimTy) $
        go retTy fixed'
    go ty (TyArg tyVar : fixed')
      | Just (tyVar', ty') <- splitForAllTy_maybe ty
      = assert (tyVar == tyVar') $
        KTExists tyVar (go ty' fixed')
    go ty (ValArg argTy : fixed')
      | Just (argTy', retTy) <- splitFunTy_maybe ty
      = assert (argTy `eqType` argTy') $
        argTy `consKT` go retTy fixed'
    go _ _
      = pprPanic "idToPKontId" (pprBndr LetBind p $$ ppr fixed)

    kontTypeToType :: KontType -> Type
    kontTypeToType = mkKontTy . mkKontArgsTy . go
      where 
        go (KTExists bndr kty) = mkUbxExistsTy bndr (go kty)
        go (KTTuple ktys)      = mkTupleTy UnboxedTuple (map go ktys)
        go (KTType ty)         = ty

    consKT :: Type -> KontType -> KontType
    ty `consKT` kty@KTExists {} = KTTuple [KTType ty, kty]
    ty `consKT` (KTTuple ktys)  = KTTuple (KTType ty : ktys)
    ty `consKT` (KTType ty2)    = KTTuple [KTType ty, KTType ty2]

-- | Remove from a list the elements corresponding to fixed arguments according
-- to the given calling convention.
filterArgs :: [a] -> KontCallConv -> [a]
filterArgs xs (ByJump fixed)
  = catMaybes (zipWith doArg xs fixed)
  where
    doArg x (ValArg _)  = Just x
    doArg x (TyArg _)   = Just x
    doArg _ _           = Nothing

-- Environment for Core -> Sequent Core translation --

data FromCoreEnv
  = FCE { fce_subst :: Subst
        , fce_currentKont :: Maybe KontId
        , fce_boundKonts :: IdEnv KontCallConv
        }

initFromCoreEnv :: FromCoreEnv
initFromCoreEnv = FCE { fce_subst = emptySubst
                      , fce_currentKont = Nothing
                      , fce_boundKonts = emptyVarEnv }

bindAsPKont :: FromCoreEnv -> PKontId -> KontCallConv -> FromCoreEnv
bindAsPKont env p conv
  = env { fce_boundKonts = extendVarEnv (fce_boundKonts env) p conv }

bindAsPKonts :: FromCoreEnv -> [(PKontId, KontCallConv)] -> FromCoreEnv
bindAsPKonts env ps = foldr (\(p, conv) env' -> bindAsPKont env' p conv) env ps

bindCurrentKont :: FromCoreEnv -> KontId -> FromCoreEnv
bindCurrentKont env p = env { fce_subst = fce_subst env `extendInScope` p
                            , fce_currentKont = Just p }

kontCallConv :: FromCoreEnv -> Var -> Maybe KontCallConv
kontCallConv env var = lookupVarEnv (fce_boundKonts env) var

fromCoreExpr :: FromCoreEnv -> Core.Expr MarkedVar -> SeqCoreKont
                            -> SeqCoreCommand
fromCoreExpr env expr (Kont fs end) = go [] env expr fs end
  where
    subst = fce_subst env
  
    go :: [SeqCoreBind] -> FromCoreEnv -> Core.Expr MarkedVar
       -> [SeqCoreFrame] -> SeqCoreEnd -> SeqCoreCommand
    go binds env expr fs end = case expr of
      Core.Var x         -> goApp x []
      Core.Lit l         -> done $ Lit l
      Core.App {}         | (Core.Var x, args) <- Core.collectArgs expr
                         -> goApp x args
      Core.App e1 e2     ->
        let e2' = fromCoreExprAsTerm env e2 mkArgKontId
        in go binds env e1 (App e2' : fs) end
      Core.Lam x e       -> done $ fromCoreLams env x e
      Core.Let bs e      ->
        let (env', bs')   = fromCoreBind env (Just (Kont fs end)) bs
        in go (bs' : binds) env' e fs end
      Core.Case e (Marked x _) ty as
        -- If the continuation is just a return, copy it into the branches
        | null fs, Return {} <- end ->
        let (subst_rhs, x') = substBndr subst x
            env_rhs = env { fce_subst = subst_rhs }
        in go binds env e [] (Case x' $ map (fromCoreAlt env_rhs (Kont fs end)) as)
        -- Otherwise be more careful. In the simplifier, we get clever and
        -- split the continuation into a duplicable part and a non-duplicable
        -- part (see splitDupableKont); for now just share the whole thing.
        | otherwise -> done $ fromCoreCaseAsTerm env e x ty as
      Core.Coercion co   -> done $ Coercion (substCo subst co)
      Core.Cast e co     -> go binds env e (Cast (substCo subst co) : fs) end
      Core.Tick ti e     -> go binds env e (Tick (substTickish subst ti) : fs) end
      Core.Type t        -> done $ Type (substTy subst t)
      where
        done term = mkCommand (reverse binds) term (Kont fs end)
        
        goApp x args = case conv_maybe of
          Just conv@(ByJump fixed)
            -> assert (length args == length fixed) $
               doneJump (filterArgs args' conv) p
          Nothing
            -> doneEval (Var x') (Kont (map App args' ++ fs) end)
          where
            x' = substIdOcc subst x
            args' = map (\e -> fromCoreExprAsTerm env e mkArgKontId) args
            conv_maybe = kontCallConv env x'
            p = let Just conv = conv_maybe in idToPKontId x' conv
            
            doneEval v k = mkCommand (reverse binds) v k
            doneJump vs j = foldr Let (Jump vs j) (reverse binds)

fromCoreLams :: FromCoreEnv -> MarkedVar -> Core.Expr MarkedVar
                            -> SeqCoreTerm
fromCoreLams env (Marked x _) expr
  = mkLambdas xs' body'
  where
    (xs, body) = Core.collectBinders expr
    bodyComm = fromCoreExpr env' body (Kont [] (Return kid))
    body' = mkCompute kid bodyComm
    (subst', xs') = substBndrs (fce_subst env) (x : map unmark xs)
    env' = env { fce_subst = subst' } `bindCurrentKont` kid
    kid = mkLamKontId ty
    ty  = substTy subst' (Core.exprType (unmarkExpr body))

fromCoreCaseAsTerm :: FromCoreEnv -> Core.Expr MarkedVar -> Core.CoreBndr -> Type
                   -> [Core.Alt MarkedVar] -> SeqCoreTerm
fromCoreCaseAsTerm env scrut bndr ty alts
  -- Translating a case naively can duplicate lots of code. Rather than
  -- copy the continuation for each branch, we bind it to a variable and
  -- copy only a Return to that binding (c.f. makeTrivial in Simpl.hs)
  --
  -- The basic plan of action (taken together with the Case clause in fromCoreExpr):
  --   [[ case e of alts ]]_k = < compute p. [[e]]_(case of [[alts]]_p) | k >
  = Compute p body
  where
    subst   = fce_subst env
    (subst', p) = substBndr subst (mkCaseKontId ty)
    env'    = env { fce_subst = subst' }
    (subst_rhs, bndr') = substBndr subst' bndr
    env_rhs = bindCurrentKont (env { fce_subst = subst_rhs }) p
    alts'   = map (fromCoreAlt env_rhs (Kont [] (Return p))) alts
    body    = fromCoreExpr env' scrut (Kont [] (Case bndr' alts'))

fromCoreExprAsTerm :: FromCoreEnv -> Core.Expr MarkedVar -> (Type -> KontId)
                                  -> SeqCoreTerm
fromCoreExprAsTerm env expr mkId
  = mkCompute k body
  where
    body = fromCoreExpr env' expr (Kont [] (Return k))
    subst = fce_subst env
    k  = asKontId $ uniqAway (substInScope subst) (mkId ty)
    ty = substTy subst (Core.exprType (unmarkExpr expr))
    env' = env `bindCurrentKont` k

fromCoreExprAsPKont :: FromCoreEnv -> SeqCoreKont -> [ArgDesc]
                    -> Core.Expr MarkedVar
                    -> SeqCorePKont
fromCoreExprAsPKont env kont descs expr
  = result
  where
    subst = fce_subst env
    
    -- Calculate outer binders (existing ones from expr, minus fixed args)
    (bndrs, body) = Core.collectBinders expr
    bndrs_unmarked = map unmark bndrs
    (subst', bndr_maybes) = mapAccumL doBndr subst (zip bndrs_unmarked descs)
    bndrs' = catMaybes bndr_maybes

    -- Calculate eta-expanding binders and arguments
    extraArgs = drop (length bndrs) descs -- will need to eta-expand with these
    (subst'', etaBndr_maybes_args) = mapAccumL mkEtaBndr subst' (zip [1..] extraArgs)
    (etaBndr_maybes, etaArgs) = unzip etaBndr_maybes_args
    etaBndrs = catMaybes etaBndr_maybes
    
    -- Eta-expand the body *before* translating to Sequent Core. This is easier
    -- than dealing with the 
    etaBody | null extraArgs = body
            | otherwise      = Core.mkApps body etaArgs
    
    env' = env { fce_subst = subst'' }
    comm = fromCoreExpr env' etaBody kont
    bndrs_final = bndrs' ++ etaBndrs
    result = PKont bndrs_final comm
    
    -- Process a binder, possibly dropping it, and return a new subst
    doBndr :: Subst -> (Var, ArgDesc) -> (Subst, Maybe Var)
    doBndr subst (bndr, FixedType ty)
      = (CoreSubst.extendTvSubst subst bndr (substTy subst ty), Nothing)
    doBndr subst (bndr, FixedVoidArg)
      -- Usually, a binder for a Void# is dead, but in case it's not, take the
      -- argument to be void#. Note that, under the let/app invariant, any
      -- argument of unlifted type must be ok-for-speculation, and any
      -- ok-for-speculation expression of Void# is equal to void# (it can't be
      -- _|_ or have side effects or possible errors and still be OFS; it could
      -- still be case x +# y of z -> void#, but then we can eliminate the case).
      -- So this is always correct.
      = (extendSubstWithVar subst bndr voidPrimId, Nothing)
    doBndr subst (bndr, TyArg _tyVar)
      = (subst', Just bndr')
      where
        (subst', bndr') = substBndr subst bndr
    doBndr subst (bndr, ValArg _)
      = (subst', Just bndr')
      where
        (subst', bndr') = substBndr subst bndr
    
    -- From an ArgDesc, generate an argument to apply and (possibly) a parameter
    -- to the eta-expanded function
    mkEtaBndr :: Subst -> (Int, ArgDesc) -> (Subst, (Maybe Var, Core.Expr MarkedVar))
    mkEtaBndr subst (_, FixedType ty)
      = (subst, (Nothing, Core.Type (substTy subst ty)))
    mkEtaBndr subst (_, FixedVoidArg)
      = (subst, (Nothing, Core.Var voidPrimId))
    mkEtaBndr subst (_, TyArg tyVar)
      = (subst', (Just tv', Core.Type (mkTyVarTy tv')))
      where
        (subst', tv') = substBndr subst tyVar
    mkEtaBndr subst (n, ValArg ty)
      = (subst', (Just x, Core.Var x))
      where
        (subst', x) = freshEtaId n subst ty
    
-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: FromCoreEnv -> SeqCoreKont -> Core.Alt MarkedVar
            -> SeqCoreAlt
fromCoreAlt env kont (ac, bs, e)
  = let (subst', bs') = substBndrs (fce_subst env) (map unmark bs)
        e' = fromCoreExpr (env { fce_subst = subst' }) e kont
    in Alt ac bs' e'

-- | Translates a Core binding into Sequent Core.
fromCoreBind :: FromCoreEnv -> Maybe SeqCoreKont -> Core.Bind MarkedVar
             -> (FromCoreEnv, SeqCoreBind)
fromCoreBind (env@FCE { fce_subst = subst }) kont_maybe bind =
  case bind of
    Core.NonRec (Marked x mark) rhs -> (env_final, NonRec pair')
      where
        (subst', x') = substBndr subst x
        env' = env { fce_subst = subst' }
        env_final | MakeKont _ <- mark = bindAsPKont env' x' conv
                  | otherwise          = env'
        (~(Just conv), pair') = fromCoreBindPair env kont_maybe x' mark rhs

    Core.Rec pairs -> (env_final, Rec pairs_final)
      where
        (subst', xs') = substRecBndrs subst (map (unmark . fst) pairs)
        env' = env { fce_subst = subst' }
        pairs_substed = [ (Marked x' mark, rhs) | (Marked _ mark, rhs) <- pairs 
                                                | x' <- xs' ]
        pairs' = [ fromCoreBindPair env_final kont_maybe x' mark rhs
                 | (Marked x' mark, rhs) <- pairs_substed ]
        env_final = bindAsPKonts env' [ (binderOfPair pair, conv)
                                      | (Just conv, pair) <- pairs' ]
        pairs_final = map snd pairs'

fromCoreBindPair :: FromCoreEnv -> Maybe SeqCoreKont -> Var -> KontOrFunc
                 -> Core.Expr MarkedVar -> (Maybe KontCallConv, SeqCoreBindPair)
fromCoreBindPair env kont_maybe x mark rhs
  = case mark of
      MakeKont fixed -> let Just kont = kont_maybe
                            pkont = fromCoreExprAsPKont env kont fixed rhs
                        in (Just (ByJump fixed),
                            BindPKont (idToPKontId x (ByJump fixed)) pkont)
      MakeFunc       -> (Nothing, BindTerm x $ fromCoreExprAsTerm env rhs mkLetKontId)

fromCoreBinds :: [Core.Bind MarkedVar] -> [SeqCoreBind]
fromCoreBinds = snd . mapAccumL (\env -> fromCoreBind env Nothing) initFromCoreEnv

------------------------------------------------
-- Public interface for Sequent Core --> Core --
------------------------------------------------
    
-- | Translates a command into Core.
commandToCoreExpr :: KontId -> SeqCoreCommand -> Core.CoreExpr
commandToCoreExpr retId comm
  = case comm of
      Let bind comm' -> Core.mkCoreLet (bindToCore (Just retId) bind)
                                       (commandToCoreExpr retId comm')
      Eval term kont -> kontToCoreExpr retId kont (termToCoreExpr term)
      Jump args j    -> Core.mkCoreApps (Core.Var (kontIdToCore retId j))
                                        (map termToCoreExpr args ++ extraArgs)
        where
          extraArgs | all isTypeTerm args = [ Core.Var voidPrimId ]
                    | otherwise           = []

-- | Translates a term into Core.
termToCoreExpr :: SeqCoreTerm -> Core.CoreExpr
termToCoreExpr val =
  case val of
    Lit l        -> Core.Lit l
    Var x        -> Core.Var x
    Lam x t      -> Core.Lam x (termToCoreExpr t)
    Type t       -> Core.Type t
    Coercion co  -> Core.Coercion co
    Compute kb c -> commandToCoreExpr kb c

type CoreContext = Core.CoreExpr -> Core.CoreExpr

-- | Translates a continuation into a function that will wrap a Core expression
-- with a fragment of context (an argument to apply to, a case expression to
-- run, etc.).
kontToCoreExpr :: KontId -> SeqCoreKont -> CoreContext
kontToCoreExpr retId (Kont fs end) =
  foldr (flip (.)) (endToCoreExpr retId end) (map frameToCoreExpr fs)

frameToCoreExpr :: SeqCoreFrame -> CoreContext
frameToCoreExpr k =
  case k of
    App  {- expr -} v   -> \e -> Core.mkCoreApp e (termToCoreExpr v)
    Cast {- expr -} co  -> \e -> Core.Cast e co
    Tick ti {- expr -}  -> \e -> Core.Tick ti e

endToCoreExpr :: KontId -> SeqCoreEnd -> CoreContext
endToCoreExpr retId k =
  case k of
    Case {- expr -} b as -> \e -> Core.Case e b (kontTyArg (idType retId))
                                                (map (altToCore retId) as)
    Return x
      | x == retId       -> \e -> e
      | otherwise        -> -- XXX Probably an error nowadays, as Return
                            -- only ever has one correct value
                            \e -> Core.App (Core.Var x) e

kontIdToCore :: Id -> KontId -> Id
kontIdToCore retId k = k `setIdType` kontTyToCoreTy argTy retTy
  where
    tyOf k = isKontTy_maybe (idType k) `orElse` pprPanic "kontIdToCore" (pprBndr LetBind k)
    argTy = tyOf k
    retTy = tyOf retId
    
kontTyToCoreTy, kontArgsTyToCoreTy :: Type -> Type -> Type
kontTyToCoreTy ty retTy
  | Just ty' <- isKontArgsTy_maybe ty
  = kontArgsTyToCoreTy ty' retTy
  | otherwise
  = mkFunTy ty retTy

kontArgsTyToCoreTy ty retTy
  | Just (a, body) <- isUbxExistsTy_maybe ty
  = mkForAllTy a (kontArgsTyToCoreTy body retTy)
  | isUnboxedTupleType ty
  = let (_, args) = splitTyConApp ty
    in if | null args -> mkFunTy voidPrimTy retTy
          | Just (a, ty') <- isUbxExistsTy_maybe (last args)
                      -> mkFunTys (init args) 
                                  (mkForAllTy a (kontArgsTyToCoreTy ty' retTy))
          | otherwise -> mkFunTys args retTy
  | otherwise
  = pprPanic "kontArgsTyToCoreTy" (ppr ty)

-- | Translates a binding into Core.
bindToCore :: Maybe KontId -> SeqCoreBind -> Core.CoreBind
bindToCore retId_maybe bind =
  case bind of
    NonRec pair -> Core.NonRec b v
      where (b, v) = bindPairToCore retId_maybe NonRecursive pair
    Rec pairs   -> Core.Rec (map (bindPairToCore retId_maybe Recursive) pairs)

bindPairToCore :: Maybe KontId -> RecFlag -> SeqCoreBindPair
               -> (Core.CoreBndr, Core.CoreExpr)
bindPairToCore retId_maybe recFlag pair =
  case pair of
    BindTerm b v -> (b, termToCoreExpr v)
    BindPKont b (PKont xs c) -> (b', Core.mkCoreLams (maybeOneShots xs')
                                                     (commandToCoreExpr retId c))
      where
        b'    = kontIdToCore retId b
        xs'   | null xs   = [ voidArgId ]
              | otherwise = xs
        maybeOneShots xs | isNonRec recFlag = map setOneShotLambdaIfId xs
                         | otherwise        = xs
        setOneShotLambdaIfId x | isId x = setOneShotLambda x
                               | otherwise = x
        retId = retId_maybe `orElse` panic "bindToCore: top-level cont"

-- | Translates a list of top-level bindings into Core.
bindsToCore :: [SeqCoreBind] -> [Core.CoreBind]
bindsToCore binds = map (bindToCore Nothing) binds

altToCore :: KontId -> SeqCoreAlt -> Core.CoreAlt
altToCore retId (Alt ac bs c) = (ac, bs, commandToCoreExpr retId c)

--------------------------------------------------------------
-- Public interface for operations going in both directions --
--------------------------------------------------------------

-- | Take an operation on Sequent Core terms and perform it on Core expressions
onCoreExpr :: (SeqCoreTerm -> SeqCoreTerm) -> (Core.CoreExpr -> Core.CoreExpr)
onCoreExpr f = termToCoreExpr . f . termFromCoreExpr

-- | Take an operation on Core expressions and perform it on Sequent Core terms
onSequentCoreTerm :: (Core.CoreExpr -> Core.CoreExpr) -> (SeqCoreTerm -> SeqCoreTerm)
onSequentCoreTerm f = termFromCoreExpr . f . termToCoreExpr

----------------
-- Miscellany --
----------------

instance Outputable EscapeAnalysis where
  ppr (EA { ea_nonEsc = nonEsc, ea_allVars = allVars })
    = text "non-escaping:" <+> ppr (mapVarEnv fst nonEsc) $$
      text "    escaping:" <+> ppr (allVars `minusVarEnv` nonEsc)
  
instance Outputable Occs where
  ppr Esc = text "esc"
  ppr (NonEsc arity calls) = text "arity" <+> int arity Out.<> comma <+>
                             speakNOf (length calls) (text "call")

instance Outputable KontOrFunc where
  ppr MakeFunc = text "func"
  ppr (MakeKont _) = text "cont"

instance Outputable MarkedVar where
  ppr (Marked var mark) = ppr var <+> brackets (ppr mark)

instance OutputableBndr MarkedVar where
  pprBndr site (Marked var MakeFunc) = pprBndr site var
  pprBndr site (Marked var mark) = pprBndr site var <+> brackets (ppr mark)
  pprPrefixOcc (Marked var _) = pprPrefixOcc var
  pprInfixOcc  (Marked var _) = pprInfixOcc  var

instance Outputable ArgDesc where
  ppr (FixedType ty) = text "fixed type:" <+> ppr ty
  ppr FixedVoidArg   = text "fixed void#"
  ppr (TyArg tyVar)  = text "type arg:" <+> pprBndr LambdaBind tyVar
  ppr (ValArg ty)    = text "arg of type" <+> ppr ty

mapCore :: (a -> b) -> Core.Expr a -> Core.Expr b
mapCore f = go
  where
    go (Core.Var x)       = Core.Var x
    go (Core.Lit l)       = Core.Lit l
    go (Core.App e1 e2)   = Core.App (go e1) (go e2)
    go (Core.Lam b e)     = Core.Lam (f b) (go e)
    go (Core.Let bind e)  = Core.Let (goBind bind) (go e)
    go (Core.Case scrut bndr ty alts)
                          = Core.Case (go scrut) (f bndr) ty
                              [ (con, map f bndrs, go rhs)
                              | (con, bndrs, rhs) <- alts ]
    go (Core.Cast e co)   = Core.Cast (go e) co
    go (Core.Tick ti e)   = Core.Tick ti (go e)
    go (Core.Type ty)     = Core.Type ty
    go (Core.Coercion co) = Core.Coercion co
    
    goBind (Core.NonRec bndr rhs) = Core.NonRec (f bndr) (go rhs)
    goBind (Core.Rec pairs)       = Core.Rec [ (f bndr, go rhs)
                                             | (bndr, rhs) <- pairs ]

unmarkExpr :: Core.Expr MarkedVar -> Core.CoreExpr
unmarkExpr = mapCore unmark

-- copied from CoreArity
freshEtaId :: Int -> Subst -> Type -> (Subst, Id)
freshEtaId n subst ty
      = (subst', eta_id')
      where
        ty'     = substTy subst ty
        eta_id' = uniqAway (substInScope subst) $
                  mkSysLocal (fsLit "eta") (mkBuiltinUnique n) ty'
        subst'  = extendInScope subst eta_id'           
