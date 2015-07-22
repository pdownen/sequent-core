{-# LANGUAGE ParallelListComp, TupleSections, CPP #-}

-- | 
-- Module      : Language.SequentCore.Simpl
-- Description : Simplifier reimplementation using Sequent Core
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- A proof of concept to demonstrate that the Sequent Core syntax can be used
-- for basic optimization in the style of GHC's simplifier. In some ways, it is
-- easier to use Sequent Core for these, as the continuations are expressed
-- directly in the program syntax rather than needing to be built up on the fly.

module Language.SequentCore.Simpl (plugin) where

import Language.SequentCore.Lint
import Language.SequentCore.OccurAnal
import Language.SequentCore.Pretty (pprTopLevelBinds)
import Language.SequentCore.Simpl.Env
import Language.SequentCore.Simpl.Monad
import Language.SequentCore.Syntax
import Language.SequentCore.Translate
import Language.SequentCore.Util
import Language.SequentCore.WiredIn

import BasicTypes
import Coercion    ( Coercion, coercionKind, isCoVar )
import CoreMonad   ( Plugin(..), SimplifierMode(..), Tick(..), CoreToDo(..),
                     CoreM, defaultPlugin, reinitializeGlobals,
                     isZeroSimplCount, pprSimplCount, putMsg, errorMsg
                   )
import CoreSyn     ( isRuntimeVar, isCheapUnfolding )
import CoreUnfold  ( smallEnoughToInline )
import DataCon
import DynFlags    ( DynFlags, gopt, GeneralFlag(..), ufKeenessFactor, ufUseThreshold )
import FastString
import Id
import HscTypes    ( ModGuts(..) )
import Literal     ( litIsDupable )
import Maybes      ( whenIsJust )
import MonadUtils
import Outputable
import Pair
import qualified PprCore as Core
import Type        ( Type, funResultTy, isUnLiftedType, mkTyVarTy )
import TysWiredIn  ( mkTupleTy )
import Var
import VarEnv
import VarSet

import Control.Exception   ( assert )
import Control.Monad       ( foldM, forM, when )

import Data.Maybe          ( isJust )

tracing, dumping, linting :: Bool
tracing = False
dumping = False
linting = True

-- | Plugin data. The initializer replaces all instances of the original
-- simplifier with the new one.
plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = \_ todos -> do
    reinitializeGlobals
    let todos' = replace todos
    return todos'
} where
  replace (CoreDoSimplify max mode : todos)
    = newPass max mode : replace todos
  replace (CoreDoPasses todos1 : todos2)
    = CoreDoPasses (replace todos1) : replace todos2
  replace (todo : todos)
    = todo : replace todos
  replace []
    = []

  newPass max mode
    = CoreDoPluginPass "SeqSimpl" (runSimplifier (3*max) mode) -- TODO Use less gas

runSimplifier :: Int -> SimplifierMode -> ModGuts -> CoreM ModGuts
runSimplifier iters mode guts
  = do
    let coreBinds = mg_binds guts
        binds = fromCoreModule coreBinds
    when linting $ whenIsJust (lintCoreBindings binds) $ \err ->
      pprPgmError "Sequent Core Lint error (pre-simpl)"
        (withPprStyle defaultUserStyle $ err
                                      $$ pprTopLevelBinds binds 
                                      $$ text "--- Original Core: ---"
                                      $$ Core.pprCoreBindings coreBinds)
    binds' <- go 1 binds
    return $ guts { mg_binds = bindsToCore binds' }
  where
    go n binds
      | n > iters
      = do
        errorMsg  $  text "Ran out of gas after"
                 <+> int iters
                 <+> text "iterations."
        return binds
      | otherwise
      = do
        let globalEnv = SimplGlobalEnv { sg_mode = mode }
            mod       = mg_module guts
            occBinds  = runOccurAnal mod binds
        when dumping $ putMsg  $ text "BEFORE" <+> int n
                              $$ text "--------" $$ pprTopLevelBinds occBinds
        (binds', count) <- runSimplM globalEnv $ simplModule occBinds
        when linting $ case lintCoreBindings binds' of
          Just err -> pprPanic "Sequent Core Lint error"
            (withPprStyle defaultUserStyle $ err $$ pprTopLevelBinds binds')
          Nothing -> return ()
        when dumping $ putMsg  $ text "SUMMARY" <+> int n
                              $$ text "---------"
                              $$ pprSimplCount count
                              $$ text "AFTER" <+> int n
                              $$ text "-------"
                              $$ pprTopLevelBinds binds'
        if isZeroSimplCount count
          then do
            when tracing $ putMsg  $  text "Done after"
                                  <+> int n <+> text "iterations"
            return binds'
          else go (n+1) binds'
    runOccurAnal mod binds
      = let isRuleActive = const False
            rules        = []
            vects        = []
            vectVars     = emptyVarSet
        in occurAnalysePgm mod isRuleActive rules vects vectVars binds

simplModule :: [InBind] -> SimplM [OutBind]
simplModule binds
  = do
    dflags <- getDynFlags
    finalEnv <- simplBinds (initialEnv dflags) binds TopLevel
    freeTick SimplifierDone
    return $ getFloatBinds (getFloats finalEnv)

simplCommandNoFloats :: SimplEnv -> InCommand -> SimplM OutCommand
simplCommandNoFloats env comm
  = do
    (env', comm') <- simplCommand (zapFloats env) comm
    return $ wrapFloats env' comm'

simplCommandNoKontFloats :: SimplEnv -> InCommand -> SimplM (SimplEnv, OutCommand)
simplCommandNoKontFloats env comm
  = do
    (env', comm') <- simplCommand (zapKontFloats env) comm
    return (zapKontFloats env', wrapKontFloats env' comm')

simplCommand :: SimplEnv -> InCommand -> SimplM (SimplEnv, OutCommand)
simplCommand env (Let bind comm)
  = do
    env' <- simplBind env bind NotTopLevel
    simplCommand env' comm
simplCommand env (Eval term kont)
  = simplCut env term (staticPart env) kont
simplCommand env (Jump args j)
  = simplJump env args j

simplTermNoFloats :: SimplEnv -> InTerm -> SimplM OutTerm
simplTermNoFloats env term
  = do
    (env', term') <- simplTerm (zapFloats env) term
    wrapFloatsAroundTerm env' term'

simplTerm :: SimplEnv -> InTerm -> SimplM (SimplEnv, OutTerm)
simplTerm env (Type ty)
  = return (env, Type (substTy env ty))
simplTerm env (Coercion co)
  = return (env, Coercion (substCo env co))
simplTerm env (Compute p comm)
  = do
    let (env', p') = enterScope env p
    -- Terms are closed with respect to continuation variables, so they can
    -- safely float past this binder. Continuations must *never* float past it,
    -- however, because they necessarily invoke the continuation bound here.
    (env'', comm') <- simplCommandNoKontFloats (zapFloats env') comm
    return (env `addFloats` env'', mkCompute p' comm')
simplTerm env v
  = do
    (env', p) <- mkFreshKontId env (fsLit "*termk") ty
    let env'' = zapFloats env'
    (env''', comm) <- simplCut env'' v (staticPart env'') (Return p)
    return (env, mkCompute p (wrapFloats env''' comm))
  where ty = substTy env (termType v)

simplBinds :: SimplEnv -> [InBind] -> TopLevelFlag
           -> SimplM SimplEnv
simplBinds env bs level
  = foldM (\env' b -> simplBind env' b level) env bs

simplBind :: SimplEnv -> InBind -> TopLevelFlag
          -> SimplM SimplEnv
--simplBind env level bind
--  | pprTraceShort "simplBind" (text "Binding" <+> parens (ppr level) <> colon <+>
--                          ppr bind) False
--  = undefined
simplBind env (NonRec (BindTerm x v)) level
  = simplNonRec env x (staticPart env) v level
simplBind env (NonRec (BindPKont p k)) _level
  = simplNonRecPKont env p (staticPart env) k
simplBind env (Rec xcs) level
  = simplRec env xcs level

simplNonRec :: SimplEnv -> InVar -> StaticEnv -> InTerm -> TopLevelFlag
            -> SimplM SimplEnv
simplNonRec env_x x env_v v level
  = do
    let (env_x', x') = enterScope env_x x
    simplLazyBind env_x' x x' env_v v level NonRecursive

simplLazyBind :: SimplEnv -> InVar -> OutVar -> StaticEnv -> InTerm -> TopLevelFlag
              -> RecFlag -> SimplM SimplEnv
simplLazyBind env_x x x' env_v v level recFlag
  | tracing
  , pprTraceShort "simplLazyBind" (ppr x <+> (if x == x' then empty else darrow <+> ppr x')
                                      <+> ppr level <+> ppr recFlag $$ ppr v) False
  = undefined
  | isTyVar x
  , Type ty <- assert (isTypeTerm v) v
  = let ty'  = substTy (env_v `inDynamicScope` env_x) ty
        tvs' = extendVarEnv (se_tvSubst env_x) x ty'
    in return $ env_x { se_tvSubst = tvs' }
  | isCoVar x
  , Coercion co <- assert (isCoTerm v) v
  = do
    co' <- simplCoercion (env_v `inDynamicScope` env_x) co
    let cvs' = extendVarEnv (se_cvSubst env_x) x co'
    return $ env_x { se_cvSubst = cvs' }
  | otherwise
  = do
    preInline <- preInlineUnconditionally env_x env_v (BindTerm x v) level
    if preInline
      then do
        tick (PreInlineUnconditionally x)
        let rhs = mkSuspension env_v v
            env' = extendIdSubst env_x x rhs
        return env'
      else do
        -- TODO Handle floating type lambdas
        let env_v' = zapFloats (env_v `inDynamicScope` env_x)
        (env_v'', v') <- simplTerm env_v' v
        -- TODO Something like Simplify.prepareRhs
        (env_x', v'')
          <- if not (doFloatFromRhs level recFlag False v' env_v')
                then do v'' <- wrapFloatsAroundTerm env_v'' v'
                        return (env_x, v'')
                else do tick LetFloatFromLet
                        return (env_x `addFloats` env_v'', v')
        completeBind env_x' x x' (Left v'') level

simplNonRecPKont :: SimplEnv -> InPKontId -> StaticEnv -> InPKont -> SimplM SimplEnv
simplNonRecPKont env_j j env_pk pk
  = assert (isPKontId j) $ do
    let (env_j', j') = enterScope env_j j
    simplPKontBind env_j' j j' env_pk pk NonRecursive

simplPKontBind :: SimplEnv -> InPKontId -> OutPKontId -> StaticEnv -> InPKont
               -> RecFlag -> SimplM SimplEnv
simplPKontBind _env_j j j' _env_pk pk recFlag
  | tracing
  , pprTraceShort "simplPKontBind" (ppr j <+> (if j == j' then empty else darrow <+> ppr j') <+>
                                    ppr recFlag $$ ppr pk) False
  = undefined
simplPKontBind env_j j j' env_pk pk _recFlag
  = do
    preInline <- preInlineUnconditionally env_j env_pk (BindPKont j pk) NotTopLevel
    if preInline
      then do
        tick (PreInlineUnconditionally j)
        let rhs = mkSuspension env_pk pk
            env' = extendPvSubst env_j j rhs
        return env'
      else do
        -- TODO Handle floating type lambdas
        let PKont xs comm = pk
            env_pk' = zapFloats (env_pk `inDynamicScope` env_j)
            (env_pk'', xs') = enterScopes env_pk' xs
        (env_with_floats, comm') <- simplCommand env_pk'' comm
        -- TODO Something like Simplify.prepareRhs
        env_j'
          <- if isEmptyFloats env_with_floats
                then return env_j
                else do tick LetFloatFromLet -- Can always float through a cont binding
                        return $ env_j `addFloats` env_with_floats
        completeBind env_j' j j' (Right (PKont xs' comm')) NotTopLevel

bindAsCurrentKont :: SimplEnv -> InKontId -> StaticEnv -> InKont -> SimplM SimplEnv
bindAsCurrentKont env_p p env_k k
  = let (env_p', _) = enterScope env_p p
    in return env_p' { se_retKont = Just (Susp env_k k) }

wrapFloatsAroundTerm :: SimplEnv -> OutTerm -> SimplM OutTerm
wrapFloatsAroundTerm env term
  | isEmptyFloats env
  = return term
  | otherwise
  = do
    let ty = termType term
    (env', k) <- mkFreshKontId env (fsLit "*wrap") ty
    return $ mkCompute k $ wrapFloats env' (mkCommand [] term (Return k))

completeNonRec :: SimplEnv -> InVar -> OutVar -> OutRhs
               -> TopLevelFlag -> SimplM SimplEnv
-- TODO Something like Simplify.prepareRhs
completeNonRec = completeBind

completeBind :: SimplEnv -> InVar -> OutVar -> OutRhs
             -> TopLevelFlag -> SimplM SimplEnv
completeBind env x x' v level
  = do
    postInline <- postInlineUnconditionally env (mkBindPair x v) level
    if postInline
      then do
        tick (PostInlineUnconditionally x)
        -- Nevermind about substituting x' for x; we'll substitute v instead
        return $ either (extendIdSubst env x . Done) (extendPvSubst env x . Done) v
      else do
        -- TODO Eta-expansion goes here
        def <- mkDef env level v
        let (env', x'') = setDef env (x' `setIdInfo` idInfo x) def
        when tracing $ liftCoreM $ putMsg (text "defined" <+> ppr x'' <+> equals <+> ppr def)
        return $ addNonRecFloat env' (mkBindPair x'' v)

mkDef :: SimplEnv -> TopLevelFlag -> OutRhs -> SimplM Definition
mkDef _env level rhs
  = do
    dflags <- getDynFlags
    -- FIXME Be smarter about this! Sometimes we want a BoundToDFun!
    -- Currently this is causing a lot of dictionaries to fail to inline
    -- at obviously desirable times.
    -- See simplUnfolding in Simplify
    return $ case rhs of
               Left term -> mkBoundTo dflags term level
               Right pkont -> mkBoundToPKont dflags pkont

-- Function named after that in GHC Simplify, so named for historical reasons it
-- seems. Basically, do completeBind but don't post-inline or do anything but
-- update the definition and float the binding.
addPolyBind :: SimplEnv -> TopLevelFlag -> OutBind -> SimplM SimplEnv
addPolyBind env level (NonRec pair)
  = do
    def <- mkDef env level (rhsOfPair pair)
    let (env', x') = setDef env (binderOfPair pair) def
    return $ addNonRecFloat env' (pair `setPairBinder` x')
addPolyBind env _level bind@(Rec _)
  -- Be conservative like the original simplifier here; recursiveness is tricky
  -- (worst case is we cause extra iteration by not updating definitions now)
  = return $ extendFloats env bind

simplRec :: SimplEnv -> [InBindPair] -> TopLevelFlag
         -> SimplM SimplEnv
simplRec env xvs level
  = do
    let (env', xs') = enterScopes env (map binderOfPair xvs)
    env'' <- foldM doBinding (zapFloats env')
               [ (x, x', v) | (x, v) <- map destBindPair xvs | x' <- xs' ]
    return $ env' `addRecFloats` env''
  where
    doBinding :: SimplEnv -> (InId, OutId, InRhs) -> SimplM SimplEnv
    doBinding env' (x, x', Left v)
      = simplLazyBind env' x x' (staticPart env') v level Recursive
    doBinding env' (p, p', Right k)
      = simplPKontBind env' p p' (staticPart env') k Recursive

-- TODO Deal with casts. Should maybe take the active cast as an argument;
-- indeed, it would make sense to think of a cut as involving a term, a
-- continuation, *and* the coercion that proves they're compatible.
simplCut :: SimplEnv -> InTerm -> StaticEnv -> InKont
                     -> SimplM (SimplEnv, OutCommand)
simplCut env_v v env_k kont
  | tracing
  , pprTraceShort "simplCut" (
      ppr env_v $$ ppr v $$ ppr env_k $$ ppr kont
    ) False
  = undefined
simplCut env_v v env_k (Return p)
  = case substKv (env_k `inDynamicScope` env_v) p of
      DoneId p'     -> simplCut2 env_v v env_k (Return p')
      Done k        -> simplCut2 env_v v (zapSubstEnvsStatic env_k) k
      Susp env_k' k -> simplCut  env_v v env_k' k
simplCut env_v v env_k k
  = simplCut2 env_v v env_k k

-- Second phase of simplCut. Now, if the continuation is a variable, it has no
-- substitution (it's a parameter). In other words, if it's a KontId, it's an
-- OutKontId.
simplCut2 :: SimplEnv -> InTerm -> StaticEnv -> InKont
                      -> SimplM (SimplEnv, OutCommand)
simplCut2 env_v (Var x) env_k kont
  = case substId env_v x of
      DoneId x'
        -> do
           term'_maybe <- callSiteInline env_v x' kont
           case term'_maybe of
             Nothing
               -> simplCut3 env_v (Var x') env_k kont
             Just term'
               -> do
                  tick (UnfoldingDone x')
                  simplCut2 (zapSubstEnvs env_v) term' env_k kont
      Done v
        -- Term already simplified (then PostInlineUnconditionally'd), so
        -- don't do any substitutions when processing it again
        -> simplCut3 (zapSubstEnvs env_v) v env_k kont
      Susp stat v
        -> simplCut2 (env_v `setStaticPart` stat) v env_k kont
simplCut2 env_v term env_k kont
  -- Proceed to phase 2
  = simplCut3 env_v term env_k kont

-- Third phase of simplCut. Now, if the term is a variable, we looked it up
-- and substituted it but decided not to inline it. (In other words, if it's an
-- id, it's an OutId.)
simplCut3 :: SimplEnv -> OutTerm -> StaticEnv -> InKont
                      -> SimplM (SimplEnv, OutCommand)
simplCut3 env_v (Type ty) _env_k kont
  = assert (isReturnKont kont) $
    let ty' = substTy env_v ty
    in return (env_v, Eval (Type ty') kont)
simplCut3 env_v (Coercion co) _env_k kont
  = assert (isReturnKont kont) $
    let co' = substCo env_v co
    in return (env_v, Eval (Coercion co') kont)
simplCut3 env_v (Lam x body) env_k (App arg kont)
  = do
    tick (BetaReduction x)
    env_v' <- simplNonRec env_v x env_k arg NotTopLevel
    simplCut env_v' body env_k kont
simplCut3 env_v (Lam x body) env_k kont
  = do
    let (env_v', x') = enterScope env_v x
    body' <- simplTermNoFloats env_v' body
    simplKontWith (env_v' `setStaticPart` env_k) (Lam x' body') kont
simplCut3 env_v term env_k kont
  | Just (value, Case x alts) <- splitValue term kont
  , Just (pairs, body) <- matchCase env_v value alts
  = do
    tick (KnownBranch x)
    env' <- foldM doPair (env_v `setStaticPart` env_k) ((x, valueToTerm value) : pairs)
    simplCommand env' body
  where
    doPair env (x, v)
      = simplNonRec env x (staticPart env_v) v NotTopLevel

-- Adapted from Simplify.rebuildCase (clause 2)
-- See [Case elimination] in Simplify
simplCut3 env_v term env_k (Case case_bndr [Alt _ bndrs rhs])
 | all isDeadBinder bndrs       -- bndrs are [InId]
 
 , if isUnLiftedType (idType case_bndr)
   then elim_unlifted        -- Satisfy the let-binding invariant
   else elim_lifted
  = do  { -- pprTraceShort "case elim" (vcat [ppr case_bndr, ppr (exprIsHNF scrut),
          --                            ppr ok_for_spec,
          --                            ppr scrut]) $
          tick (CaseElim case_bndr)
        ; env' <- simplNonRec (env_v `setStaticPart` env_k)
                    case_bndr (staticPart env_v) term NotTopLevel
        ; simplCommand env' rhs }
  where
    elim_lifted   -- See Note [Case elimination: lifted case]
      = termIsHNF env_v term
     || (is_plain_seq && ok_for_spec)
              -- Note: not the same as exprIsHNF
     || case_bndr_evald_next rhs
 
    elim_unlifted
      -- TODO This code, mostly C&P'd from Simplify.rebuildCase, illustrates a
      -- problem: Here we want to know something about the computation that
      -- computed the term we're cutting the Case with. This makes sense in
      -- original Core because we can just look at the scrutinee. Right here,
      -- though, we are considering the very moment of interaction between
      -- scrutinee *term* and case statement; information about how the term
      -- came to be, which is crucial to whether the case can be eliminated, is
      -- not available.
      --
      -- I'm hand-waving a bit here; in fact, if we have 
      --   case launchMissiles# 4# "Russia"# of _ -> ...,
      -- then in Sequent Core we have
      --   < launchMissiles# | $ 4#; $ "Russia"#; case of [ _ -> ... ] >,
      -- where the case is buried in the continuation. The code at hand won't
      -- even see this. But if we wait until simplKont to do case elimination,
      -- we may miss the chance to match a term against a more interesting
      -- continuation. It will be found in the next iteration, but this seems
      -- likely to make several iterations often necessary (whereas the GHC
      -- simplifier rarely even takes more than two iterations).
      | is_plain_seq = termOkForSideEffects term
            -- The entire case is dead, so we can drop it,
            -- _unless_ the scrutinee has side effects
      | otherwise    = ok_for_spec
            -- The case-binder is alive, but we may be able
            -- turn the case into a let, if the expression is ok-for-spec
            -- See Note [Case elimination: unlifted case]
 
    -- Same objection as above applies. termOkForSideEffects and
    -- termOkForSpeculation are almost never true unless the term is a
    -- Compute, which is not typical.
    ok_for_spec      = termOkForSpeculation term
    is_plain_seq     = isDeadBinder case_bndr -- Evaluation *only* for effect
 
    case_bndr_evald_next :: SeqCoreCommand -> Bool
      -- See Note [Case binder next]
    case_bndr_evald_next (Eval (Var v) _) = v == case_bndr
    case_bndr_evald_next _                = False
      -- Could allow for let bindings,
      -- but the original code in Simplify suggests doing so would be expensive

simplCut3 env_v (Compute p c) env_k kont
  = do
    env_v' <- bindAsCurrentKont env_v p env_k kont
    simplCommand env_v' c
simplCut3 env_v term@(Lit {}) env_k kont
  = simplKontWith (env_v `setStaticPart` env_k) term kont
simplCut3 env_v term@(Var {}) env_k kont
  = simplKontWith (env_v `setStaticPart` env_k) term kont

-- TODO Somehow handle updating Definitions with NotAmong values?
matchCase :: SimplEnv -> InValue -> [InAlt]
          -> Maybe ([(InVar, InTerm)], InCommand)
-- Note that we assume that any variable whose definition is a case-able value
-- has already been inlined by callSiteInline. So we don't check variables at
-- all here. GHC instead relies on CoreSubst.exprIsConApp_maybe to work this out
-- (before call-site inlining is even considered). I think GHC effectively
-- decides it's *always* a good idea to inline a known constructor being cased,
-- code size be damned, which seems pretty defensible given how these things
-- tend to cascade.
matchCase _env_v (LitVal lit) (Alt (LitAlt lit') xs body : _alts)
  | assert (null xs) True
  , lit == lit'
  = Just ([], body)
matchCase _env_v (ConsVal ctor _tyArgs valArgs) (Alt (DataAlt ctor') xs body : _alts)
  | ctor == ctor'
  , assert (length valArgs == length xs) True
  = Just (zip xs valArgs, body)
matchCase env_v value (Alt DEFAULT xs body : alts)
  | assert (null xs) True
  = Just $ matchCase env_v value alts `orElse` ([], body)
matchCase env_v value (_ : alts)
  = matchCase env_v value alts
matchCase _ _ []
  = Nothing

simplKont :: SimplEnv -> InKont -> SimplM (SimplEnv, OutKont)
simplKont env kont
  | tracing
  , pprTraceShort "simplKont" (
      ppr env $$ ppr kont
    ) False
  = undefined
simplKont env kont
  = go env kont (\k -> k)
  where
    go :: SimplEnv -> InKont -> (OutKont -> OutKont) -> SimplM (SimplEnv, OutKont)
    go env kont _
      | tracing
      , pprTraceShort "simplKont::go" (
          ppr env $$ ppr kont
        ) False
      = undefined
    go env (App arg kont) kc
      -- TODO Handle strict arguments differently? GHC detects whether arg is
      -- strict, but here we've lost that information.
      = do
        -- Don't float out of arguments (see Simplify.rebuildCall)
        arg' <- simplTermNoFloats env arg
        go env kont (kc . App arg')
    go env (Cast co kont) kc
      = do
        co' <- simplCoercion env co
        go env kont (kc . Cast co')
    go env (Case x alts) kc
      = do
        env' <- case alts of
                  -- We're about to fork the context, thus duplicating the return
                  -- continuation, so now's when we make sure it's okay to duplicate it.
                  (_:_:_) -> ensureRetKontDupable env
                  _       -> return env
        let (env'', x') = enterScope env' x
        -- FIXME The Nothing there could be the scrutinee, but we don't ever
        -- have access to it here.
        alts' <- forM alts (simplAlt env'' Nothing [] x)
        -- FIXME We're forgetting that we made the ret cont dupable! Can this
        -- be a problem? (Maybe not: How can there be another reference to it if
        -- we just split its scope for the first time?)
        
        -- Long-term solution is to have a sequent-aware occurrence analyser so
        -- we can know from the start whether we need to duplicate a
        -- continuation (the binder would say whether it's used in multiple
        -- branches).
        return (env `addFloats` env', kc (Case x' alts'))
    go env (Tick ti kont) kc
      = go env kont (kc . Tick ti)
    go env (Return x) kc
      -- TODO Consider call-site inline
      = case substKv env x of
          DoneId x'
            -> return (env, kc (Return x'))
          Done k
            -> go (zapSubstEnvs env) k kc
          Susp stat k
            -> go (env `setStaticPart` stat) k kc

simplKontWith :: SimplEnv -> OutTerm -> InKont -> SimplM (SimplEnv, OutCommand)
simplKontWith env term kont
  = do
    (env', kont') <- simplKont env kont
    return (env', mkCommand [] term kont')

simplAlt :: SimplEnv -> Maybe OutValue -> [AltCon] -> OutId -> InAlt -> SimplM OutAlt
simplAlt env _scrut_maybe _notAmong _caseBndr (Alt con xs c)
  = do
    -- TODO Important: Update definitions! This is likely to be low-hanging
    -- fruit. This is why we take the scrutinee, other constructors, and case
    -- binder as arguments.
    let (env', xs') = enterScopes env xs
    c' <- simplCommandNoFloats env' c
    return $ Alt con xs' c'

simplCoercion :: SimplEnv -> Coercion -> SimplM Coercion
simplCoercion env co =
  -- TODO Actually simplify
  return $ substCo env co

simplVar :: SimplEnv -> InVar -> SimplM OutTerm
simplVar env x
  | isTyVar x = return $ Type (substTyVar env x)
  | isCoVar x = return $ Coercion (substCoVar env x)
  | otherwise
  = case substId env x of
    DoneId x' -> return $ Var x'
    Done v -> return v
    Susp stat v -> simplTermNoFloats (env `setStaticPart` stat) v

simplJump :: SimplEnv -> [InArg] -> InPKontId -> SimplM (SimplEnv, OutCommand)
simplJump env args j
  | tracing
  , pprTrace "simplJump" (ppr env $$ parens (pprWithCommas ppr args) $$ ppr j)
    False
  = undefined
simplJump env args j
  = do
    case substPv env j of
      DoneId j'
        -> do
           -- FIXME Call site inline!!
           (env', args') <- mapAccumLM simplTerm env args
           return (env', Jump args' j')
      Done pk
        -> reduce (zapSubstEnvs env) pk
      Susp stat pk
        -> reduce (env `setStaticPart` stat) pk
  where
    reduce env_pk (PKont xs comm)
      = do
        env_comm <- foldM bindArg env_pk (zip xs args)
        simplCommand env_comm comm
    bindArg env_x (x, arg)
      = simplNonRec env_x x (staticPart env) arg NotTopLevel

-- Based on preInlineUnconditionally in SimplUtils; see comments there
preInlineUnconditionally :: SimplEnv -> StaticEnv -> InBindPair
                         -> TopLevelFlag -> SimplM Bool
preInlineUnconditionally _env_x _env_rhs pair level
  = do
    ans <- go <$> getMode <*> getDynFlags
    --liftCoreM $ putMsg $ "preInline" <+> ppr x <> colon <+> text (show ans))
    return ans
  where
    x = binderOfPair pair
  
    go mode dflags
      | not active                              = False
      | not enabled                             = False
      | TopLevel <- level, isBottomingId x      = False
      -- TODO Somehow GHC can pre-inline an exported thing? We can't, anyway
      | isExportedId x                          = False
      | isCoVar x                               = False
      | otherwise = case idOccInfo x of
                      IAmDead                  -> True
                      OneOcc inLam True intCxt -> try_once inLam intCxt
                      _                        -> False
      where
        active = isActive (sm_phase mode) act
        act = idInlineActivation x
        enabled = gopt Opt_SimplPreInlining dflags
        try_once inLam intCxt
          | not inLam = isNotTopLevel level || early_phase
          | BindTerm _ rhs <- pair = intCxt && canInlineTermInLam rhs
          | otherwise = False
        canInlineInLam k c
          | Just v <- asValueCommand k c = canInlineTermInLam v
          | otherwise                    = False
        canInlineTermInLam (Lit _)       = True
        canInlineTermInLam (Lam x t)     = isRuntimeVar x
                                         || canInlineTermInLam t
        canInlineTermInLam (Compute k c) = canInlineInLam k c
        canInlineTermInLam _             = False
        early_phase = case sm_phase mode of
                        Phase 0 -> False
                        _       -> True

-- Based on postInlineUnconditionally in SimplUtils; see comments there
postInlineUnconditionally :: SimplEnv -> OutBindPair -> TopLevelFlag
                          -> SimplM Bool
postInlineUnconditionally _env pair level
  = do
    ans <- go <$> getMode <*> getDynFlags
    -- liftCoreM $ putMsg $ "postInline" <+> ppr x <> colon <+> text (show ans)
    return ans
  where
    go mode dflags
      | not active                  = False
      | isWeakLoopBreaker occ_info  = False
      | isExportedId x              = False
      | isTopLevel level            = False
      | either isTrivialTerm isTrivialPKont rhs = True
      | otherwise
      = case occ_info of
          OneOcc in_lam _one_br int_cxt
            ->     smallEnoughToInline dflags unfolding
               && (not in_lam ||
                    (isCheapUnfolding unfolding && int_cxt))
          IAmDead -> True
          _ -> False

      where
        (x, rhs) = destBindPair pair
        occ_info = idOccInfo x
        active = isActive (sm_phase mode) (idInlineActivation x)
        unfolding = idUnfolding x

-- Heavily based on section 7 of the Secrets paper (JFP version)
callSiteInline :: SimplEnv -> InVar -> InKont
               -> SimplM (Maybe OutTerm)
callSiteInline env_v x kont
  = do
    ans <- go <$> getMode <*> getDynFlags
    when tracing $ liftCoreM $ putMsg $ ans `seq`
      hang (text "callSiteInline") 6 (pprBndr LetBind x <> colon
        <+> (if isJust ans then text "YES" else text "NO") $$ ppr def)
    return ans
  where
    go _mode _dflags
      | Just (BoundTo rhs level guid) <- def
      , shouldInline env_v rhs (idOccInfo x) level guid kont
      = Just rhs
      | Just (BoundToDFun bndrs con args) <- def
      = inlineDFun env_v bndrs con args kont
      | otherwise
      = Nothing
    def = findDef env_v x

shouldInline :: SimplEnv -> OutTerm -> OccInfo -> TopLevelFlag -> Guidance
             -> InKont -> Bool
shouldInline env rhs occ level guid kont
  = case occ of
      IAmALoopBreaker weak
        -> weak -- inline iff it's a "rule-only" loop breaker
      IAmDead
        -> pprPanic "shouldInline" (text "dead binder")
      OneOcc True True _ -- occurs once, but inside a non-linear lambda
        -> whnfOrBot env rhs && someBenefit env rhs level kont
      OneOcc False False _ -- occurs in multiple branches, but not in lambda
        -> inlineMulti env rhs level guid kont
      _
        -> whnfOrBot env rhs && inlineMulti env rhs level guid kont

someBenefit :: SimplEnv -> OutTerm -> TopLevelFlag -> InKont -> Bool
someBenefit env rhs level kont
  | termIsConstruction rhs, Case {} <- kont
  = True
  | Lit {} <- rhs, Case {} <- kont
  = True
  | Lam {} <- rhs
  = consider xs args
  | otherwise
  = False
  where
    (xs, _)       = lambdas rhs
    (args, kont') = collectArgs kont

    -- See Secrets, section 7.2, for the someBenefit criteria
    consider :: [OutVar] -> [InTerm] -> Bool
    consider [] (_:_)      = True -- (c) saturated call in interesting context
    consider [] []         | Case {} <- kont' = True -- (c) ditto
                           -- Check for (d) saturated call to nested
                           | otherwise = isNotTopLevel level
    consider (_:_) []      = False -- unsaturated
                           -- Check for (b) nontrivial or known-var argument
    consider (_:xs) (a:as) = nontrivial a || knownVar a || consider xs as
    
    nontrivial arg   = not (isTrivialTerm arg)
    knownVar (Var x) = x `elemVarEnv` se_defs env
    knownVar _       = False

whnfOrBot :: SimplEnv -> OutTerm -> Bool
whnfOrBot _ (Lam {})  = True
whnfOrBot _ term      = any ($ term) [isTrivialTerm, termIsBottom, termIsConstruction]

inlineMulti :: SimplEnv -> OutTerm -> TopLevelFlag -> Guidance -> InKont -> Bool
inlineMulti env rhs level guid kont
  = noSizeIncrease rhs kont
    || someBenefit env rhs level kont && smallEnough env rhs guid kont

noSizeIncrease :: OutTerm -> InKont -> Bool
noSizeIncrease _rhs _kont = False --TODO

smallEnough :: SimplEnv -> OutTerm -> Guidance -> InKont -> Bool
smallEnough _ _ Never _ = False
smallEnough _env term (Usually unsatOk boringOk) kont
  = (unsatOk || not unsat) && (boringOk || not boring)
  where
    unsat = length valArgs < termArity term
    (_, valArgs, _) = collectTypeAndOtherArgs kont
    boring = isReturnKont kont

smallEnough env _term (Sometimes bodySize argWeights resWeight) kont
  -- The Formula (p. 40)
  = bodySize - sizeOfCall - keenness `times` discounts <= threshold
  where
    (_, args, kont') = collectTypeAndOtherArgs kont
    sizeOfCall           | null args =  0 -- a lone variable or polymorphic value
                         | otherwise = 10 * (1 + length args)
    keenness             = ufKeenessFactor (se_dflags env)
    discounts            = argDiscs + resDisc
    threshold            = ufUseThreshold (se_dflags env)
    argDiscs             = sum $ zipWith argDisc args argWeights
    argDisc arg w        | isEvald arg = w
                         | otherwise   = 0
    resDisc              | length args > length argWeights || isCase kont'
                         = resWeight
                         | otherwise = 0

    isEvald term         = termIsHNF env term

    isCase (Case {})     = True
    isCase _             = False

    real `times` int     = ceiling (real * fromIntegral int)

inlineDFun :: SimplEnv -> [Var] -> DataCon -> [OutTerm] -> InKont -> Maybe OutTerm
inlineDFun _env bndrs con conArgs kont
--  | pprTraceShort "inlineDFun" (sep ([ppr bndrs, ppr con, ppr conArgs, ppr kont, ppr args, ppr kont']) $$
--      if enoughArgs && kontIsCase env kont' then text "YES" else text "NO") False
--  = undefined
  | enoughArgs, Case {} <- kont'
  = Just term
  | otherwise
  = Nothing
  where
    (args, kont') = collectArgsUpTo (length bndrs) kont
    enoughArgs    = length args == length bndrs
    term          = mkLambdas bndrs bodyTerm
    bodyTerm      = mkAppTerm (Var (dataConWorkId con)) conArgs

ensureRetKontDupable :: SimplEnv -> SimplM SimplEnv
ensureRetKontDupable env
  | se_retKontDupable env
  = return env
  | otherwise
  -- Arguably, se_retKont and se_retKontDupable are redundant; as of this
  -- writing, se_retKontDupable is False iff se_retKont is Just (Susp _ _). This
  -- seems like a fragile circumstance, though.
  = case se_retKont env of
      Just (Done k)          -> warnPprTrace True __FILE__ __LINE__
                                (text "OutKont not marked as dupable in env:" <+> ppr k)
                                return env_markedDupable
      Just (DoneId {})       -> return env_markedDupable
      Nothing                -> return env_markedDupable
      Just (Susp env_k kont) -> do
                                (env', kont') <- mkDupableKont (env_k `inDynamicScope` env) ty kont
                                return (env' `setStaticPart` staticPart env)
                                         { se_retKont = Just (Done kont')
                                         , se_retKontDupable = True }
  where
    env_markedDupable = env { se_retKontDupable = True }
    retId = se_retId env `orElse` panic "ensureRetKontDupable at top level"
    ty = kontTyArg (idType retId)

-- | Make a continuation into something we're okay with duplicating into each
-- branch of a case (and each branch of those branches, ...), possibly
-- generating a number of bound terms and join points in the process.
--
-- The rules:
--   1. Duplicate returns.
--   2. Duplicate casts.
--   3. Don't duplicate ticks (because GHC doesn't).
--   4. Duplicate applications, but ANF-ize them first to share the arguments.
--   5. Don't duplicate cases (!) because, unlike with Simplify.mkDupableCont,
--        we don't need to (see comment in Case clause). But "ANF-ize" in a dual
--        sense by creating a join point for each branch.
--   6. Don't duplicate lambdas (they're usually already join points!).

mkDupableKont :: SimplEnv -> Type -> InKont -> SimplM (SimplEnv, OutKont)
mkDupableKont env ty kont
  = do
    when tracing $ liftCoreM $ putMsg $ hang (text "mkDupableKont") 4 (ppr env $$ ppr kont)
    (env', ans) <- go env (\kont' -> kont') ty kont
    when tracing $ liftCoreM $ putMsg $ hang (text "mkDupableKont DONE") 4 $
      ppr ans $$ vcat (map ppr (getFloatBinds (getFloats env')))
    return (env', ans)
  where
    -- The OutKont -> OutKont is a continuation for the outer continuation (!!).
    go :: SimplEnv -> (OutKont -> OutKont) -> Type -> InKont
       -> SimplM (SimplEnv, OutKont)
    go env kk ty (Return kid)
      = case substKv env kid of
          DoneId kid'               -> return (env, kk (Return kid'))
          Done   kont'              -> do
                                       let env' = zapFloats (zapSubstEnvs env)
                                       go env' kk ty kont'
          Susp stat kont'           -> do
                                       let env' = zapFloats (stat `inDynamicScope` env)
                                       go env' kk ty kont'
    
    go env kk _ty (Cast co kont)
      = do
        co' <- simplCoercion env co
        go env (kk . Cast co') (pSnd (coercionKind co')) kont
    
    go env kk ty kont@(Tick {})
      = split env kk ty kont
    
    go env kk ty (App arg kont)
      = do
        (env', arg') <- mkDupableTerm env arg
        go env' (kk . App arg') (funResultTy ty) kont

    -- Don't duplicate seq (see Note [Single-alternative cases] in GHC Simplify.lhs)
    go env kk ty kont@(Case caseBndr [Alt _altCon bndrs _rhs])
      | all isDeadBinder bndrs
      , not (isUnLiftedType (idType caseBndr))
      = split env kk ty kont

    go env kk _ty (Case caseBndr alts)
      -- This is dual to the App case: We have several branches and we want to
      -- bind each to a join point.
      = do
        -- NOTE: At this point, mkDupableCont in GHC Simplify.lhs calls
        -- prepareCaseCont (ultimately a recursive call) on the outer
        -- continuation. We have no outer continuation for a case; in the
        -- equivalent situation, we would have already dealt with the outer
        -- case. May be worth checking that we get the same result.
        
        let (altEnv, caseBndr') = enterScope env caseBndr
        alts' <- mapM (simplAlt altEnv Nothing [] caseBndr) alts
        (env', alts'') <- mkDupableAlts env caseBndr alts'
        
        return (env', kk (Case caseBndr' alts''))
        
    split :: SimplEnv -> (OutKont -> OutKont) -> Type -> InKont
          -> SimplM (SimplEnv, OutKont)
    split env kk ty kont
        -- XXX This is a bit ugly, but it is currently the only way to split a
        -- non-parameterized continuation in two:
        --   Edup[Knodup] ==> let cont j x = < x | Knodup >
        --                    in Edup[case of x -> < jump x | j >]
        -- Notice that it's only okay to put the case there because Knodup is a
        -- strict context, which is only necessarily true because all
        -- continuations are strict contexts. If that changes, we'll need to
        -- revisit this.
      = do
        let kontTy = mkKontTy (mkKontArgsTy (mkTupleTy UnboxedTuple [ty]))
        (env', j) <- mkFreshVar env (fsLit "*tickj") kontTy
        let (env'', x) = enterScope env' (mkKontArgId ty)
            join_rhs  = PKont [x] (Eval (Var x) kont)
            join_kont = Case x [Alt DEFAULT [] (Jump [Var x] j)]
        env_final <- simplNonRecPKont env'' j (staticPart env'') join_rhs
        
        return (env_final, kk join_kont)
    
mkDupableTerm :: SimplEnv -> InTerm
                        -> SimplM (SimplEnv, OutTerm)
mkDupableTerm env term
  -- TODO Can't check the term for triviality first, since it is an InTerm and
  -- may need to be simplified. Maybe we should take an OutTerm instead?
  --  | isTrivialTerm term
  --  = return (env, term)
  --  | otherwise
  = do
    (env', bndr) <- mkFreshVar env (fsLit "triv") (substTy env (termType term))
    env'' <- simplLazyBind env' bndr bndr (staticPart env') term NotTopLevel NonRecursive
    term_final <- simplVar env'' bndr
    return (env'', term_final)

mkDupableAlts :: SimplEnv -> OutId -> [InAlt] -> SimplM (SimplEnv, [InAlt])
mkDupableAlts env caseBndr = mapAccumLM (\env' -> mkDupableAlt env' caseBndr) env

mkDupableAlt :: SimplEnv -> OutId -> InAlt -> SimplM (SimplEnv, InAlt)
mkDupableAlt env caseBndr alt@(Alt altCon bndrs rhs)
  = do
    dflags <- getDynFlags
    if commandIsDupable dflags rhs
      then return (env, alt)
      else do
        -- TODO Update definition of case binder! Importantly, we should update
        -- the unfolding attached to the lambda-bound version of the case binder
        -- because, unlike most unfoldings, that one cannot be recreated from
        -- context.
        
        let used_bndrs | isDeadBinder caseBndr = filter abstract_over bndrs
                       | otherwise = bndrs ++ [caseBndr]
                  
            abstract_over bndr
                | isTyVar bndr = True -- Abstract over all type variables just in case
                | otherwise    = not (isDeadBinder bndr)
                -- The deadness info on the new Ids is preserved by simplBinders_
        
        let (tyBndrs, valBndrs) = span isTyVar used_bndrs
            bndrTys = map idType valBndrs
            argTy   = mkKontArgsTy $ foldr mkUbxExistsTy (mkTupleTy UnboxedTuple bndrTys) tyBndrs
        
        (_, join_bndr) <- mkFreshVar env (fsLit "*j") (mkKontTy argTy)
        
        let join_rhs  = PKont used_bndrs rhs
            join_args = map (Type . mkTyVarTy) tyBndrs ++ map Var valBndrs
            join_comm = Jump join_args join_bndr
        
        when tracing $ liftCoreM $
          putMsg (text "created join point" <+> pprBndr LetBind join_bndr $$
                  ppr join_rhs $$
                  ppr (Alt altCon bndrs join_comm))
        
        env' <- addPolyBind env NotTopLevel (NonRec (BindPKont join_bndr join_rhs))
        return (env', Alt altCon bndrs join_comm)
            
commandIsDupable :: DynFlags -> SeqCoreCommand -> Bool
commandIsDupable dflags c
  = isJust (go dupAppSize (C c))
  where
    go n (C (Eval v k))    = go n  (T v) >>= \n' ->
                             go n' (K k)
  
    go n (T (Type {}))     = Just n
    go n (T (Coercion {})) = Just n
    go n (T (Var {}))      = decrement n
    go n (T (Lit lit))     | litIsDupable dflags lit = decrement n
    
    go n (K (Tick _ k))    = go n (K k)
    go n (K (Cast _ k))    = go n (K k)
    go n (K (App f k))     = go n  (T f) >>= \n' ->
                             go n' (K k)
    
    go _ _ = Nothing

    decrement :: Int -> Maybe Int
    decrement 0 = Nothing
    decrement n = Just (n-1)

-- see GHC CoreUtils.lhs
dupAppSize :: Int
dupAppSize = 8
