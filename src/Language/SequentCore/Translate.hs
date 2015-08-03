{-# LANGUAGE ParallelListComp, TupleSections #-}

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
  commandToCoreExpr, termToCoreExpr, kontToCoreExpr,
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
import Id
import Maybes
import qualified MkCore as Core
import MkId
import Outputable  hiding ( (<>) )
import Type        hiding ( substTy )
import TysPrim
import TysWiredIn
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
  = EA { ea_freeVars :: FreeSet  -- ^ Which variables, among the candidates,
                                 --   appear free in the expression (escaping or
                                 --   otherwise).
       , ea_escVars  :: EscSet } -- ^ Of the variables in ea_freeVars, which
                                 --   ones appear in escaping contexts.
       
type FreeSet = IdSet
type EscSet  = IdSet

emptyEscapeAnalysis :: EscapeAnalysis
emptyEscapeAnalysis = EA { ea_freeVars = emptyVarSet
                         , ea_escVars  = emptyVarSet }

unitNonEscVar :: Id -> EscapeAnalysis
unitNonEscVar x = emptyEscapeAnalysis { ea_freeVars = unitVarSet x }

unitEscVar :: Id -> EscapeAnalysis
unitEscVar x = emptyEscapeAnalysis { ea_freeVars = unitVarSet x
                                   , ea_escVars = unitVarSet x }

markAllAsEscaping :: EscapeAnalysis -> EscapeAnalysis
markAllAsEscaping escs@(EA { ea_freeVars = fvs, ea_escVars = evs })
  = assert (evs `subVarSet` fvs) $ escs { ea_escVars = fvs }

combineEscapeAnalyses :: EscapeAnalysis -> EscapeAnalysis -> EscapeAnalysis
combineEscapeAnalyses (EA fvs1 evs1) (EA fvs2 evs2)
  = EA (fvs1 `unionVarSet` fvs2) (evs1 `unionVarSet` evs2)

forgetVars :: EscapeAnalysis -> [Id] -> EscapeAnalysis
forgetVars (EA fvs evs) xs = EA (fvs `delVarSetList` xs) (evs `delVarSetList` xs)

occursIn, escapesIn, occursWithoutEscapingIn :: Var -> EscapeAnalysis -> Bool
x `occursIn` ea                = x `elemVarSet` ea_freeVars ea
x `escapesIn` ea               = x `elemVarSet` ea_escVars ea
x `occursWithoutEscapingIn` ea = x `occursIn` ea && not (x `escapesIn` ea)

-- | True if both:
--     1. At least one of the variables occurs
--     2. None of the variables escapes
listOccursWithoutEscapingIn :: [Var] -> EscapeAnalysis -> Bool
xs `listOccursWithoutEscapingIn` ea
  = any (`occursIn` ea) xs && not (any (`escapesIn` ea) xs)

instance Monoid EscapeAnalysis where
  mempty = emptyEscapeAnalysis
  mappend = combineEscapeAnalyses

-- Top-down data --

type TotalArity = Arity -- Counts *all* arguments, including types
newtype Candidacy = Candidate TotalArity
type BindingInfo = Candidacy
type BindingEnv = IdEnv BindingInfo

emptyBindingEnv :: BindingEnv
emptyBindingEnv = emptyVarEnv

-- Monad --

-- | The monad underlying the escape analysis.
newtype EscM a = EscM { unEscM :: BindingEnv -> (EscapeAnalysis, a) }

instance Monad EscM where
  return x = EscM $ \_   -> (emptyEscapeAnalysis, x)
  m >>= k  = EscM $ \env -> let (escs1, x) = unEscM m env
                                (escs2, y) = unEscM (k x) env
                            in (escs1 <> escs2, y)

instance Functor EscM where fmap = liftM
instance Applicative EscM where { pure = return; (<*>) = ap }

instance MonadFix EscM where
  mfix f = EscM $ \env -> let pair@(_, ans) = unEscM (f ans) env
                          in pair

runEscM :: EscM a -> a
runEscM m = snd $ unEscM m emptyBindingEnv

-- Monad operations --

getBindings :: EscM BindingEnv
getBindings = EscM $ \env -> (emptyEscapeAnalysis, env)

alteringEnv :: (BindingEnv -> BindingEnv) -> EscM a -> EscM a
alteringEnv f m = EscM $ \env -> unEscM m (f env)

withBindings :: BindingEnv -> EscM a -> EscM a
withBindings env m = EscM $ \_ -> unEscM m env

withoutBinding :: Id -> EscM a -> EscM a
withoutBinding x m = alteringEnv (`delVarEnv` x) m

withoutBindingList :: [Id] -> EscM a -> EscM a
withoutBindingList xs m = alteringEnv (`delVarEnvList` xs) m

reportNonEscVar :: Id -> EscM ()
reportNonEscVar x = writeAnalysis (unitNonEscVar x)

reportEscVar :: Id -> EscM ()
reportEscVar x = writeAnalysis (unitEscVar x)

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

data KontOrFunc = MakeKont TotalArity | MakeFunc
data MarkedVar = Marked Var KontOrFunc

unmark :: MarkedVar -> Var
unmark (Marked var _) = var

-- Escape analysis --

escAnalProgram :: Core.CoreProgram -> [Core.Bind MarkedVar]
escAnalProgram binds = runEscM (go binds)
  where
    go :: [Core.CoreBind] -> EscM [Core.Bind MarkedVar]
    go (bind:binds)
      = do
        (_escs, bind', binds') <- mfix $ \ ~(rec_escs_body, _, _) -> do
          (env', bind') <- escAnalBind TopLevel bind rec_escs_body
          (escs_body, binds') <- readAnalysis $ withBindings env' $ go binds
          return (escs_body, bind', binds')
        return (bind':binds')
    go [] = return []
    
escAnalBind :: TopLevelFlag -> Core.CoreBind -> EscapeAnalysis -> EscM (BindingEnv, Core.Bind MarkedVar)
escAnalBind lvl (Core.NonRec bndr rhs) escs_body
  = do
    (env', [Candidate arity]) <- addBinders [(bndr, rhs)]
    (escs_rhs, rhs') <- captureAnalysis $ escAnalExpr rhs
    let kontify = isNotTopLevel lvl && bndr `occursWithoutEscapingIn` escs_body
        (mark, escs_rhs') | kontify   = (MakeKont arity, escs_rhs)
                          | otherwise = (MakeFunc, markAllAsEscaping escs_rhs)
    writeAnalysis escs_rhs'
    return (env', Core.NonRec (Marked bndr mark) rhs')

escAnalBind lvl (Core.Rec pairs) escs_body
  = do
    (env', cands) <- addBinders pairs
    let (bndrs, rhss) = unzip pairs
    (escs_rhss, rhss') <- captureAnalysis $ withBindings env' $ mapM escAnalExpr rhss
    let escs = escs_rhss <> escs_body
        kontify = isNotTopLevel lvl &&
                  bndrs `listOccursWithoutEscapingIn` escs
        mark arity | kontify   = MakeKont arity
                   | otherwise = MakeFunc
        pairs' = [ (Marked bndr (mark arity), rhs')
                 | bndr <- bndrs | rhs' <- rhss' | Candidate arity <- cands ]
        escs_rhss' | not kontify = markAllAsEscaping escs_rhss
                   | otherwise   = escs_rhss
    writeAnalysis (escs_rhss' `forgetVars` bndrs)
    return (env', Core.Rec pairs')

addBinders :: [(Var, Core.CoreExpr)] -> EscM (BindingEnv, [Candidacy])
addBinders pairs
  = do
    env <- getBindings
    return $ mapAccumL doOne env pairs
  where
    doOne env (bndr, rhs)
      = (extendVarEnv env bndr cand, cand)
      where
        (bndrs, _body) = Core.collectBinders rhs
        cand = Candidate (length bndrs)
   
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
    body' <- withoutBindingList valBndrs $
             -- Lambdas ruin contification, so pretend the free vars escape
             filterAnalysis markAllAsEscaping $
             escAnalExpr body
    let bndrs' = [ Marked bndr MakeFunc | bndr <- tyBndrs ++ valBndrs ]
    return $ Core.mkLams bndrs' body'
escAnalExpr (Core.Let bind body)
  = do
    (_escs, bind', body') <- mfix $ \ ~(rec_escs_body, _, _) -> do
      (env', bind') <- escAnalBind NotTopLevel bind rec_escs_body
      (escs_body, body') <- readAnalysis $ withBindings env' $ escAnalExpr body
      return (escs_body, bind', body')
    return $ Core.Let bind' body'
escAnalExpr (Core.Case scrut bndr ty alts)
  = do
    scrut' <- filterAnalysis markAllAsEscaping $ escAnalExpr scrut
    alts' <- withoutBinding bndr $ forM alts $ \(con, bndrs, rhs) -> do
      rhs' <- withoutBindingList bndrs $ escAnalExpr rhs
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
    env <- getBindings
    let valArgs = filter (not . Core.isTypeArg) args
    case lookupVarEnv env fid of
      Just (Candidate arity) ->
        -- Exactly saturated calls don't cause escapes; others do
        if arity == length valArgs
          then reportNonEscVar fid
          else reportEscVar fid
      _ -> return ()
    args' <- forM args $ \arg ->
      filterAnalysis markAllAsEscaping $ escAnalExpr arg
    escAnalId fid
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
  = void $ withoutBindingList bndrs $ escAnalExpr rhs
escAnalRule _
  = return ()

escAnalUnfolding :: Core.Unfolding -> EscM ()
escAnalUnfolding (Core.CoreUnfolding { Core.uf_tmpl = rhs  }) = void $ escAnalExpr rhs
escAnalUnfolding (Core.DFunUnfolding { Core.df_args = args }) = mapM_ escAnalExpr args
escAnalUnfolding _                                            = return ()

----------------------------------------
-- Phase 2: Translate to Sequent Core --
----------------------------------------

data FromCoreEnv
  = FCE { fce_subst :: Subst
        , fce_currentKont :: Maybe KontId
        , fce_boundKonts :: IdEnv KontCallConv
        }

data KontCallConv = ByJump TotalArity VoidArgFlag
data VoidArgFlag = HasVoidArg | NoVoidArg

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
fromCoreExpr env expr kont = go [] env expr kont
  where
    subst = fce_subst env
  
    go :: [SeqCoreBind] -> FromCoreEnv -> Core.Expr MarkedVar
       -> SeqCoreKont -> SeqCoreCommand
    go binds env expr kont = case expr of
      Core.Var x         -> goApp x []
      Core.Lit l         -> done $ Lit l
      Core.App {}         | (Core.Var x, args) <- Core.collectArgs expr
                         -> goApp x args
      Core.App e1 e2     ->
        let e2' = fromCoreExprAsTerm env e2 mkArgKontId
        in go binds env e1 (App e2' kont)
      Core.Lam x e       -> done $ fromCoreLams env x e
      Core.Let bs e      ->
        let (env', bs')   = fromCoreBind env (Just kont) bs
        in go (bs' : binds) env' e kont
      Core.Case e (Marked x _) ty as
        -- If the continuation is just a return, copy it into the branches
        | Return {} <- kont ->
        let (subst_rhs, x') = substBndr subst x
            env_rhs = env { fce_subst = subst_rhs }
        in go binds env e (Case x' $ map (fromCoreAlt env_rhs kont) as)
        -- Otherwise be more careful. In the simplifier, we get clever and
        -- split the continuation into a duplicable part and a non-duplicable
        -- part (see splitDupableKont); for now just share the whole thing.
        | otherwise -> done $ fromCoreCaseAsTerm env e x ty as
      Core.Coercion co   -> done $ Coercion (substCo subst co)
      Core.Cast e co     -> go binds env e (Cast (substCo subst co) kont)
      Core.Tick ti e     -> go binds env e (Tick (substTickish subst ti) kont)
      Core.Type t        -> done $ Type (substTy subst t)
      where
        done term = mkCommand (reverse binds) term kont
        
        goApp x args = case conv_maybe of
          Just (ByJump arity HasVoidArg) -> assert (length args == arity + 1) $
                                            doneJump (dropLast args') p
          Just (ByJump arity NoVoidArg)  -> assert (length args == arity) $
                                            doneJump args' p
          Nothing             -> doneEval (Var x') (foldr App kont args')
          where
            x' = substIdOcc subst x
            args' = map (\e -> fromCoreExprAsTerm env e mkArgKontId) args
            conv_maybe = kontCallConv env x'
            p = let Just conv = conv_maybe in idToKontId x' conv
            doneEval v k = mkCommand (reverse binds) v k
            doneJump vs j = foldr Let (Jump vs j) (reverse binds)

dropLast :: [a] -> [a]
dropLast [] = panic "dropLast"
dropLast [_] = []
dropLast (x:xs) = x:dropLast xs

fromCoreLams :: FromCoreEnv -> MarkedVar -> Core.Expr MarkedVar
                            -> SeqCoreTerm
fromCoreLams env (Marked x _) expr
  = mkLambdas xs' body'
  where
    (xs, body) = Core.collectBinders expr
    bodyComm = fromCoreExpr env' body (Return kid)
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
    alts'   = map (fromCoreAlt env_rhs (Return p)) alts
    body    = fromCoreExpr env' scrut (Case bndr' alts')

fromCoreExprAsTerm :: FromCoreEnv -> Core.Expr MarkedVar -> (Type -> KontId)
                                  -> SeqCoreTerm
fromCoreExprAsTerm env expr mkId
  = mkCompute k body
  where
    body = fromCoreExpr env' expr (Return k)
    subst = fce_subst env
    k  = asKontId $ uniqAway (substInScope subst) (mkId ty)
    ty = substTy subst (Core.exprType (unmarkExpr expr))
    env' = env `bindCurrentKont` k

fromCoreExprAsPKont :: FromCoreEnv -> SeqCoreKont -> TotalArity
                    -> Core.Expr MarkedVar
                    -> (KontCallConv, SeqCorePKont)
fromCoreExprAsPKont env kont arity expr
  = (conv, PKont bndrs_final comm)
  where
    (bndrs, body) = collectNBinders arity expr
    subst = fce_subst env
    (subst', bndrs_final) = substBndrs subst bndrs'
    bndrs_unmarked = map unmark bndrs
    (hasVoid, bndrs')
      = case span isTyVar bndrs_unmarked of
          (tyVars, [x]) | isDeadBinder x
                        , idType x `eqType` voidPrimTy
             -> (True, tyVars)
          _  -> (False, bndrs_unmarked)
    conv | hasVoid   = ByJump (arity - 1) HasVoidArg
         | otherwise = ByJump arity NoVoidArg
    env' = env { fce_subst = subst' }
    comm = fromCoreExpr env' body kont

collectNBinders :: TotalArity -> Core.Expr MarkedVar -> ([MarkedVar], Core.Expr MarkedVar)
collectNBinders 0 expr = ([], expr)
collectNBinders n (Core.Lam x body) | n > 0 = (x:xs, body')
  where
    (xs, body') = collectNBinders (n - 1) body
collectNBinders n body = pprPanic "collectNBinders" (int n <+> ppr body)

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
      MakeKont arity -> let Just kont = kont_maybe
                            (conv, pkont) = fromCoreExprAsPKont env kont arity rhs
                        in (Just conv,
                            BindPKont (idToKontId x conv) pkont)
      MakeFunc       -> (Nothing, BindTerm x $ fromCoreExprAsTerm env rhs mkLetKontId)

idToKontId :: Id -> KontCallConv -> KontId
idToKontId p (ByJump arity _hasVoidArg)
  = p `setIdType` mkKontTy (mkKontArgsTy (foldr mkUbxExistsTy (mkTupleTy UnboxedTuple kArgTys) tyVars))
    where
      (tyVars, monoTy) = splitForAllTys (idType p)
      (argTys, _retTy) = splitFunTys monoTy
      kArgTys          = take arity argTys

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

-- | Translates a continuation into a function that will wrap a Core expression
-- with a fragment of context (an argument to apply to, a case expression to
-- run, etc.).
kontToCoreExpr :: KontId -> SeqCoreKont -> (Core.CoreExpr -> Core.CoreExpr)
kontToCoreExpr retId k e =
  case k of
    App  {- expr -} v k'      -> kontToCoreExpr retId k' (Core.mkCoreApp e (termToCoreExpr v))
    Case {- expr -} b as      -> Core.Case e b (kontTyArg (idType retId)) (map (altToCore retId) as)
    Cast {- expr -} co k'     -> kontToCoreExpr retId k' (Core.Cast e co)
    Tick ti {- expr -} k'     -> kontToCoreExpr retId k' (Core.Tick ti e)
    Return x
      | x == retId            -> e
      | otherwise             -> -- XXX Probably an error nowadays, as Return
                                 -- only ever has one correct value
                                 Core.App (Core.Var x) e

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
        args' | null args = [ voidPrimTy ]
              | otherwise = args
    in mkFunTys args' retTy
  | otherwise
  = pprPanic "kontArgsTyToCoreTy" (ppr ty)

needsVoidArg :: Type -> Bool
needsVoidArg ty
  | Just ty' <- isKontArgsTy_maybe ty
  = go ty'
  | otherwise
  = False
  where
    go ty' | Just (_, bodyTy) <- isUbxExistsTy_maybe ty'
           = go bodyTy
           | isUnboxedTupleType ty'
           = let (_, args) = splitTyConApp ty
             in null args
           | otherwise
           = pprPanic "needsVoidArg" (ppr ty)

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
