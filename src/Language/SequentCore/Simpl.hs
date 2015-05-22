{-# LANGUAGE ParallelListComp #-}

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

import Language.SequentCore.Pretty (pprTopLevelBinds)
import Language.SequentCore.Simpl.Env
import Language.SequentCore.Simpl.Monad
import Language.SequentCore.Syntax
import Language.SequentCore.Translate

import BasicTypes
import Coercion    ( isCoVar )
import CoreMonad   ( Plugin(..), SimplifierMode(..), Tick(..), CoreToDo(..),
                     CoreM, defaultPlugin, reinitializeGlobals, errorMsg,
                     isZeroSimplCount, putMsg
                   )
import CoreSyn     ( isRuntimeVar, isCheapUnfolding )
import CoreUnfold  ( smallEnoughToInline )
import DynFlags    ( gopt, GeneralFlag(..), ufKeenessFactor, ufUseThreshold )
import FastString
import Id
import HscTypes    ( ModGuts(..) )
import Maybes
import MonadUtils  ( mapAccumLM )
import OccurAnal   ( occurAnalysePgm )
import Outputable
import Type        ( Type, isUnLiftedType )
import Var
import VarEnv
import VarSet

import Control.Applicative ( (<$>), (<*>) )
import Control.Exception   ( assert )
import Control.Monad       ( when, foldM )

tracing :: Bool
tracing = False

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
    = CoreDoPluginPass "SeqSimpl" (runSimplifier max mode)

runSimplifier :: Int -> SimplifierMode -> ModGuts -> CoreM ModGuts
runSimplifier iters mode guts
  = go 1 guts
  where
    go n guts
      | n > iters
      = do
        errorMsg  $  text "Ran out of gas after"
                 <+> int iters
                 <+> text "iterations."
        return guts
      | otherwise
      = do
        let globalEnv = SimplGlobalEnv { sg_mode = mode }
            mod       = mg_module guts
            coreBinds = mg_binds guts
            occBinds  = runOccurAnal mod coreBinds
            binds     = fromCoreBinds occBinds
        when tracing $ putMsg  $ text "BEFORE" <+> int n
                              $$ text "--------" $$ pprTopLevelBinds binds
        (binds', count) <- runSimplM globalEnv $ simplModule binds
        when tracing $ putMsg  $ text "AFTER" <+> int n
                              $$ text "-------" $$ pprTopLevelBinds binds'
        let coreBinds' = bindsToCore binds'
            guts'      = guts { mg_binds = coreBinds' }
        when tracing $ putMsg  $ text "CORE AFTER" <+> int n
                              $$ text "------------" $$ ppr coreBinds'
        if isZeroSimplCount count
          then do
            when tracing $ putMsg  $  text "Done after"
                                  <+> int n <+> text "iterations"
            return guts'
          else go (n+1) guts'
    runOccurAnal mod core
      = let isRuleActive = const False
            rules        = []
            vects        = []
            vectVars     = emptyVarSet
        in occurAnalysePgm mod isRuleActive rules vects vectVars core

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

simplCommand :: SimplEnv -> InCommand -> SimplM (SimplEnv, OutCommand)
simplCommand env (Command { cmdLet = binds, cmdValue = val, cmdCont = cont })
  = do
    env' <- simplBinds env binds NotTopLevel
    simplCut env' val (staticPart env') cont

simplValueNoFloats :: SimplEnv -> InValue -> SimplM OutValue
simplValueNoFloats env val
  = do
    (env', val') <- simplValue (zapFloats env) val
    return $ wrapFloatsAroundValue env' val'

simplValue :: SimplEnv -> InValue -> SimplM (SimplEnv, OutValue)
simplValue _env (Cont {})
  = panic "simplValue"
simplValue env v
  = do
    (env'', comm) <- simplCut env' v (staticPart env') Return
    return (env'', mkCompute comm)
  where env' = zapCont env

simplBinds :: SimplEnv -> [InBind] -> TopLevelFlag
           -> SimplM SimplEnv
simplBinds env bs level
  = foldM (\env b -> simplBind env (staticPart env) b level) env bs

simplBind :: SimplEnv -> StaticEnv -> InBind -> TopLevelFlag
          -> SimplM SimplEnv
--simplBind env level bind
--  | pprTrace "simplBind" (text "Binding" <+> parens (ppr level) <> colon <+>
--                          ppr bind) False
--  = undefined
simplBind env_x env_c (NonRec x c) level
  = simplNonRec env_x x env_c c level
simplBind env_x env_c (Rec xcs) level
  = simplRec env_x env_c xcs level

simplNonRec :: SimplEnv -> InVar -> StaticEnv -> InValue -> TopLevelFlag
            -> SimplM SimplEnv
simplNonRec env_x x env_v v level
  = do
    let (env_x', x') = enterScope env_x x
    simplLazyBind env_x' x x' env_v v level NonRecursive

simplLazyBind :: SimplEnv -> InVar -> OutVar -> StaticEnv -> InValue -> TopLevelFlag
              -> RecFlag -> SimplM SimplEnv
simplLazyBind env_x x x' env_v v level isRec
  | isTyVar x
  , Type ty <- assert (isTypeValue v) v
  = let ty'  = substTyStatic env_v ty
        tvs' = extendVarEnv (se_tvSubst env_x) x ty'
    in return $ env_x { se_tvSubst = tvs' }
  | isCoVar x
  , Coercion co <- assert (isCoValue v) v
  -- TODO Simplify coercions; for now, just apply substitutions
  = let co'  = substCoStatic env_v co
        cvs' = extendVarEnv (se_cvSubst env_x) x co'
    in return $ env_x { se_cvSubst = cvs' }
  | otherwise
  = do
    preInline <- preInlineUnconditionally env_x x env_v v level
    if preInline
      then do
        tick (PreInlineUnconditionally x)
        let rhs = mkSuspension env_v v
            env' = extendIdSubst env_x x rhs
        return env'
      else case v of
        Cont cont
          -> do
             let env_v' = zapFloats (env_x `setStaticPart` env_v)
             (env_v'', cont') <- simplCont env_v' cont
             -- Remember, env_v' may contain floated bindings, without which
             -- cont' is invalid. Therefore we either float them past here by
             -- adding them to the outer environment or wrap cont' in them now.
             (env_x', rhs')
               <- if not (doFloatFromRhs level NonRecursive False (Cont cont') env_v'')
                     then do -- Not floating past here, so wrap RHS and discard 
                             -- its environment
                             cont'' <- wrapFloatsAroundCont env_v'' (idType x) cont'
                             return (env_x, Cont cont'')
                     else do -- Float up from the RHS by adding floats to the
                             -- outer environment
                             tick LetFloatFromLet
                             return (addFloats env_x env_v'', Cont cont')
             completeBind env_x' x x' rhs' level
        _ -> do
             -- TODO Handle floating type lambdas
             let env_v' = zapFloats (env_x `setStaticPart` env_v)
             (env_v'', v') <- simplValue env_v' v
             -- TODO Something like Simplify.prepareRhs
             (env_x', v'')
               <- if not (doFloatFromRhs level NonRecursive False v' env_v'')
                     then return (env_x, wrapFloatsAroundValue env_v'' v')
                     else do tick LetFloatFromLet
                             return (addFloats env_x env_v'', v')
             completeBind env_x' x x' v'' level

wrapFloatsAroundCont :: SimplEnv -> Type -> OutCont -> SimplM OutCont
wrapFloatsAroundCont env inTy cont
  | isEmptyFloats env
  = return cont
  | otherwise
  -- Remember, all nontrivial continuations are strict contexts. Therefore it's
  -- always okay to rewrite
  --   E ==> case of [ a -> <a | E> ]
  -- *except* for E = Return. However, we only call this when something's being
  -- floated from a continuation, and it seems unlikely we'd be floating a let
  -- from a Return.
  = do
    id <- mkSysLocalM (fsLit "$in") inTy
    let comm = wrapFloats env (mkCommand [] (Var id) cont)
    return $ Case id inTy [Alt DEFAULT [] comm] Return

wrapFloatsAroundValue :: SimplEnv -> OutValue -> OutValue
wrapFloatsAroundValue env val
  | isEmptyFloats env
  = val
  | not (isProperValue val)
  = panic "wrapFloatsAroundValue"
wrapFloatsAroundValue env val
  = mkCompute $ wrapFloats env (valueCommand val)

completeBind :: SimplEnv -> InVar -> OutVar -> OutValue -> TopLevelFlag
             -> SimplM SimplEnv
completeBind env x x' v level
  = do
    postInline <- postInlineUnconditionally env x v level
    if postInline
      then do
        tick (PostInlineUnconditionally x)
        -- Nevermind about substituting x' for x; we'll substitute v instead
        return $ extendIdSubst env x (DoneVal v)
      else do
        -- TODO Eta-expansion goes here
        dflags <- getDynFlags
        let ins   = se_inScope env
            defs  = se_defs env
            x''   = x' `setIdInfo` idInfo x
            ins'  = extendInScopeSet ins x''
            defs' = extendVarEnv defs x'' (mkBoundTo dflags v (idOccInfo x'') level)
            env'  = env { se_inScope = ins', se_defs = defs' }
        return $ addNonRecFloat env' x'' v

simplRec :: SimplEnv -> StaticEnv -> [(InVar, InValue)] -> TopLevelFlag
         -> SimplM SimplEnv
simplRec env_x env_v xvs level
  = do
    let (env_x', xs') = enterScopes env_x (map fst xvs)
    env_x'' <- foldM doPair (zapFloats env_x') 
                [ (x, x', v) | (x, v) <- xvs | x' <- xs' ] 
    return $ env_x' `addRecFloats` env_x''
  where
    doPair :: SimplEnv -> (InId, OutId, InValue) -> SimplM SimplEnv
    doPair env_x (x, x', v)
      = simplLazyBind env_x x x' env_v v level Recursive

-- TODO Deal with casts. Should maybe take the active cast as an argument;
-- indeed, it would make sense to think of a cut as involving a value, a
-- continuation, *and* the coercion that proves they're compatible.
simplCut :: SimplEnv -> InValue -> StaticEnv -> InCont
                     -> SimplM (SimplEnv, OutCommand)
{-
simplCut env_v v env_k cont
  | pprTrace "simplCut" (
      ppr env_v $$ ppr v $$ ppr env_k $$ ppr cont
    ) False
  = undefined
-}
simplCut env_v (Var x) env_k cont
  = case substId env_v x of
      DoneId x'
        -> do
           val'_maybe <- callSiteInline env_v x cont
           case val'_maybe of
             Nothing
               -> simplCut2 env_v (Var x') env_k cont
             Just val'
               -> simplCut (zapSubstEnvs env_v) val' env_k cont
      DoneVal v
        -- Value already simplified (then PostInlineUnconditionally'd), so
        -- don't do any substitutions when processing it again
        -> simplCut2 (zapSubstEnvs env_v) v env_k cont
      SuspVal stat v
        -> simplCut (env_v `setStaticPart` stat) v env_k cont
simplCut env_v val env_k cont
  -- Proceed to phase 2
  = simplCut2 env_v val env_k cont

-- Second phase of simplCut. Now, if the value is a variable, we looked it up
-- and substituted it but decided not to inline it. (In other words, if it's an
-- id, it's an OutId.)
simplCut2 :: SimplEnv -> OutValue -> StaticEnv -> InCont
                      -> SimplM (SimplEnv, OutCommand)
simplCut2 env_v (Type ty) _env_k cont
  = assert (isReturnCont cont) $
    let ty' = substTy env_v ty
    in return (env_v, valueCommand (Type ty'))
simplCut2 env_v (Coercion co) _env_k cont
  = assert (isReturnCont cont) $
    let co' = substCo env_v co
    in return (env_v, valueCommand (Coercion co'))
simplCut2 _env_v (Cont {}) _env_k _cont
  = panic "simplCut of cont"
simplCut2 env_v (Lam x c) env_k (App arg cont)
  = do
    tick (BetaReduction x)
    env_v' <- simplNonRec env_v x env_k arg NotTopLevel
    -- Effectively, here we bind the covariable in the lambda to the current
    -- continuation before proceeding
    simplCommand (bindCont env_v' env_k cont) c
simplCut2 env_v (Lam x c) env_k cont
  = do
    let (env_v', x') = enterScope env_v x
    c' <- simplCommandNoFloats (zapCont env_v') c
    simplContWith (env_v' `setStaticPart` env_k) (Lam x' c') cont
simplCut2 env_v val env_k (Case x _ alts cont)
  | isManifestValue val
  , Just (pairs, body) <- matchCase env_v val alts
  = do
    tick (KnownBranch x)
    env' <- foldM doPair (env_v `setStaticPart` env_k) ((x, val) : pairs)
    simplCommand (env' `pushCont` cont) body
  where
    isManifestValue (Lit {})  = True
    isManifestValue (Cons {}) = True
    isManifestValue _         = False
    
    doPair env (x, v)
      = simplNonRec env x (staticPart env_v) v NotTopLevel

-- Adapted from Simplify.rebuildCase (clause 2)
-- See [Case elimination] in Simplify
simplCut2 env_v val env_k (Case case_bndr ty [Alt _ bndrs rhs] cont)
 | all isDeadBinder bndrs       -- bndrs are [InId]
 
 , if isUnLiftedType ty
   then elim_unlifted        -- Satisfy the let-binding invariant
   else elim_lifted
  = do  { -- pprTrace "case elim" (vcat [ppr case_bndr, ppr (exprIsHNF scrut),
          --                            ppr ok_for_spec,
          --                            ppr scrut]) $
          tick (CaseElim case_bndr)
        ; env' <- simplNonRec (env_v `setStaticPart` env_k)
                    case_bndr (staticPart env_v) val NotTopLevel
        ; simplCommand (env' `pushCont` cont) rhs }
  where
    elim_lifted   -- See Note [Case elimination: lifted case]
      = valueIsHNF env_v val
     || (is_plain_seq && ok_for_spec)
              -- Note: not the same as exprIsHNF
     || case_bndr_evald_next rhs
 
    elim_unlifted
      -- TODO This code, mostly C&P'd from Simplify.rebuildCase, illustrates a
      -- problem: Here we want to know something about the computation that
      -- computed the value we're cutting the Case with. This makes sense in
      -- original Core because we can just look at the scrutinee. Right here,
      -- though, we are considering the very moment of interaction between
      -- scrutinee *value* and case statement; information about how the value
      -- came to be, which is crucial to whether the case can be eliminated, is
      -- not available.
      --
      -- I'm hand-waving a bit here; in fact, if we have 
      --   case launchMissiles# 4# "Russia"# of _ -> ...,
      -- then in Sequent Core we have
      --   < launchMissiles# | $ 4#; $ "Russia"#; case of [ _ -> ... ] >,
      -- where the case is buried in the continuation. The code at hand won't
      -- even see this. But if we wait until simplCont to do case elimination,
      -- we may miss the chance to match a value against a more interesting
      -- continuation. It will be found in the next iteration, but this seems
      -- likely to make several iterations often necessary (whereas the GHC
      -- simplifier rarely even takes more than two iterations).
      | is_plain_seq = valueOkForSideEffects val
            -- The entire case is dead, so we can drop it,
            -- _unless_ the scrutinee has side effects
      | otherwise    = ok_for_spec
            -- The case-binder is alive, but we may be able
            -- turn the case into a let, if the expression is ok-for-spec
            -- See Note [Case elimination: unlifted case]
 
    -- Same objection as above applies. valueOkForSideEffects and
    -- valueOkForSpeculation are almost never true unless the value is a
    -- Compute, which is not typical.
    ok_for_spec      = valueOkForSpeculation val
    is_plain_seq     = isDeadBinder case_bndr -- Evaluation *only* for effect
 
    case_bndr_evald_next :: SeqCoreCommand -> Bool
      -- See Note [Case binder next]
    case_bndr_evald_next (Command [] (Var v) _) = v == case_bndr
    case_bndr_evald_next _                      = False
      -- Could allow for let bindings,
      -- but the original code in Simplify suggests doing so would be expensive

simplCut2 env_v (Cons ctor args) env_k cont
  = do
    (env_v', args') <- mapAccumLM simplValue env_v args
    simplContWith (env_v' `setStaticPart` env_k) (Cons ctor args') cont
simplCut2 env_v (Compute c) env_k cont
  = simplCommand (bindCont env_v env_k cont) c
simplCut2 env_v val@(Lit {}) env_k cont
  = simplContWith (env_v `setStaticPart` env_k) val cont
simplCut2 env_v val@(Var {}) env_k cont
  = simplContWith (env_v `setStaticPart` env_k) val cont

-- TODO Somehow handle updating Definitions with NotAmong values?
matchCase :: SimplEnv -> InValue -> [InAlt]
          -> Maybe ([(InVar, InValue)], InCommand)
-- Note that we assume that any variable whose definition is a case-able value
-- has already been inlined by callSiteInline. So we don't check variables at
-- all here. GHC instead relies on CoreSubst.exprIsConApp_maybe to work this out
-- (before call-site inlining is even considered). I think GHC effectively
-- decides it's *always* a good idea to inline a known constructor being cased,
-- code size be damned, which seems pretty defensible given how these things
-- tend to cascade.
matchCase _env_v (Lit lit) (Alt (LitAlt lit') xs body : _alts)
  | assert (null xs) True
  , lit == lit'
  = Just ([], body)
matchCase _env_v (Cons ctor args) (Alt (DataAlt ctor') xs body : _alts)
  | ctor == ctor'
  , assert (length valArgs == length xs) True
  = Just (zip xs valArgs, body)
  where
    -- TODO Check that this is the Right Thing even in the face of GADTs and
    -- other shenanigans.
    valArgs = filter (not . isTypeValue) args
matchCase env_v val (Alt DEFAULT xs body : alts)
  | assert (null xs) True
  , valueIsHNF env_v val -- case is strict; don't match if not evaluated
  = Just $ matchCase env_v val alts `orElse` ([], body)
matchCase env_v val (_ : alts)
  = matchCase env_v val alts
matchCase _ _ []
  = Nothing

simplCont :: SimplEnv -> InCont -> SimplM (SimplEnv, OutCont)
{-
simplCont env cont
  | pprTrace "simplCont" (
      ppr env $$ ppr cont
    ) False
  = undefined
-}
simplCont env cont
  = go env cont (\k -> k)
  where
    {-
    go env cont _
      | pprTrace "simplCont::go" (
          ppr cont
        ) False
      = undefined
    -}
    go :: SimplEnv -> InCont -> (OutCont -> OutCont) -> SimplM (SimplEnv, OutCont)
    go env (App arg cont) kc
      -- TODO Handle strict arguments differently? GHC detects whether arg is
      -- strict, but here we've lost that information.
      = do
        -- Don't float out of arguments (see Simplify.rebuildCall)
        arg' <- simplValueNoFloats env arg
        go env cont (kc . App arg')
    go env (Cast co cont) kc
      -- TODO Simplify coercions
      = go env cont (kc . Cast co)
    go env (Case x ty alts cont) kc
      = do
        (env', cont', x') <- consider env cont
        alts' <- mapM (doCase env') alts
        go env cont' (kc . Case x' (substTy env ty) alts')
      where
        consider env cont@(Jump {})
          = do
            -- This is a "mu_beta-reduction", where the binder is the implicit
            -- one for the current continuation. We make up an id for this.
            currentContId <-
              asContId <$> mkSysLocalM (fsLit "$currentCont") (substTy env ty)
            tick (BetaReduction currentContId)
            consider (bindCont env (staticPart env) cont) Return
        consider env (Case x2 ty2 alts2 cont2)
          = do
            tick (CaseOfCase x2)
            consider (bindCont env (staticPart env) (Case x2 ty2 alts2 Return))
                       cont2
        consider env cont
          = let (env', x') = enterScope env x
            in return (env', cont, x')
        doCase env' (Alt con xs c)
          = do
            let (env'', xs') = enterScopes env' xs
            c' <- simplCommandNoFloats env'' c
            return $ Alt con xs' c'
    go env (Tick ti cont) kc
      = go env cont (kc . Tick ti)
    go env (Jump x) kc
      -- TODO Consider call-site inline
      = case substId env x of
          DoneId x'
            -> return (env, kc (Jump x'))
          DoneVal (Cont k)
            -> go (zapSubstEnvs env) k kc
          SuspVal stat (Cont k)
            -> go (env `setStaticPart` stat) k kc
          _
            -> panic "jump to non-continuation"
    go env Return kc
      | Just (env', cont) <- restoreEnv env
      = go env' cont kc
      | otherwise
      = return (env, kc Return)

simplContWith :: SimplEnv -> OutValue -> InCont -> SimplM (SimplEnv, OutCommand)
simplContWith env val cont
  = do
    (env', cont') <- simplCont env cont
    return (env', mkCommand [] val cont')

-- Based on preInlineUnconditionally in SimplUtils; see comments there
preInlineUnconditionally :: SimplEnv -> InVar -> StaticEnv -> InValue
                         -> TopLevelFlag -> SimplM Bool
preInlineUnconditionally _env_x x _env_rhs rhs level
  = do
    ans <- go <$> getMode <*> getDynFlags
    --liftCoreM $ putMsg $ "preInline" <+> ppr x <> colon <+> text (show ans))
    return ans
  where
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
          | otherwise = intCxt && canInlineValInLam rhs
        canInlineInLam c
          | Just v <- asValueCommand c  = canInlineValInLam v
          | otherwise                   = False
        canInlineValInLam (Lit _)       = True
        canInlineValInLam (Lam x c)     = isRuntimeVar x || canInlineInLam c
        canInlineValInLam (Compute c)   = canInlineInLam c
        canInlineValInLam _             = False
        early_phase = case sm_phase mode of
                        Phase 0 -> False
                        _       -> True

-- Based on postInlineUnconditionally in SimplUtils; see comments there
postInlineUnconditionally :: SimplEnv -> OutVar -> OutValue -> TopLevelFlag
                          -> SimplM Bool
postInlineUnconditionally _env x v level
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
      | isTrivialValue v            = True
      | otherwise
      = case occ_info of
          OneOcc in_lam _one_br int_cxt
            -- TODO Actually update unfoldings so that this makes sense
            ->     smallEnoughToInline dflags unfolding
               && (not in_lam ||
                    (isCheapUnfolding unfolding && int_cxt))
          IAmDead -> True
          _ -> False

      where
        occ_info = idOccInfo x
        active = isActive (sm_phase mode) (idInlineActivation x)
        unfolding = idUnfolding x

-- Heavily based on section 7 of the Secrets paper (JFP version)
callSiteInline :: SimplEnv -> InVar -> InCont
               -> SimplM (Maybe OutValue)
callSiteInline env_v x cont
  = do
    ans <- go <$> getMode <*> getDynFlags
    -- liftCoreM $ putMsg $ text "callSiteInline" <+> pprBndr LetBind x <> colon <+> ppr ans
    return ans
  where
    go _mode _dflags
      | Just (BoundTo rhs occ level guid) <- lookupVarEnv (se_defs env_v) x
      , shouldInline env_v rhs occ level guid cont
      = Just rhs
      | otherwise
      = Nothing

shouldInline :: SimplEnv -> OutValue -> OccInfo -> TopLevelFlag -> Guidance
             -> InCont -> Bool
shouldInline env rhs occ level guid cont
  = case occ of
      IAmALoopBreaker weak
        -> weak -- inline iff it's a "rule-only" loop breaker
      IAmDead
        -> pprPanic "shouldInline" (text "dead binder")
      OneOcc True True _ -- occurs once, but inside a non-linear lambda
        -> whnfOrBot env rhs && someBenefit env rhs level cont
      OneOcc False False _ -- occurs in multiple branches, but not in lambda
        -> inlineMulti env rhs level guid cont
      _
        -> whnfOrBot env rhs && inlineMulti env rhs level guid cont

someBenefit :: SimplEnv -> OutValue -> TopLevelFlag -> InCont -> Bool
someBenefit env rhs level cont
  | Cons {} <- rhs, Case {} <- cont
  = True
  | Lit {} <- rhs, Case {} <- cont
  = True
  | Lam {} <- rhs
  = consider xs args
  | otherwise
  = False
  where
    (xs, _) = collectLambdas rhs
    (args, cont') = collectArgs cont

    -- See Secrets, section 7.2, for the someBenefit criteria
    consider :: [OutVar] -> [InValue] -> Bool
    consider [] (_:_)      = True -- (c) saturated call in interesting context
    consider [] []         | Case {} <- cont' = True -- (c) ditto
                           -- Check for (d) saturated call to nested
                           | otherwise = isNotTopLevel level
    consider (_:_) []      = False -- unsaturated
                           -- Check for (b) nontrivial or known-var argument
    consider (_:xs) (a:as) = nontrivial a || knownVar a || consider xs as
    
    nontrivial arg   = not (isTrivialValue arg)
    knownVar (Var x) = x `elemVarEnv` se_defs env
    knownVar _       = False

whnfOrBot :: SimplEnv -> OutValue -> Bool
whnfOrBot _ (Cons {}) = True
whnfOrBot _ (Lam {})  = True
whnfOrBot _ val       = isTrivialValue val || valueIsBottom val

inlineMulti :: SimplEnv -> OutValue -> TopLevelFlag -> Guidance -> InCont -> Bool
inlineMulti env rhs level guid cont
  = noSizeIncrease rhs cont
    || someBenefit env rhs level cont && smallEnough env rhs guid cont

noSizeIncrease :: OutValue -> InCont -> Bool
noSizeIncrease _rhs _cont = False --TODO

smallEnough :: SimplEnv -> OutValue -> Guidance -> InCont -> Bool
smallEnough _ _ Never _ = False
smallEnough env _val (Sometimes bodySize argWeights resWeight) cont
  -- The Formula (p. 40)
  = bodySize - sizeOfCall - keenness `times` discounts <= threshold
  where
    (_, args, cont') = collectTypeAndOtherArgs cont
    sizeOfCall           | null args =  0 -- a lone variable or polymorphic value
                         | otherwise = 10 * (1 + length args)
    keenness             = ufKeenessFactor (se_dflags env)
    discounts            = argDiscs + resDisc
    threshold            = ufUseThreshold (se_dflags env)
    argDiscs             = sum $ zipWith argDisc args argWeights
    argDisc arg w        | isEvald arg = w
                         | otherwise   = 0
    resDisc              | length args > length argWeights || isCase cont'
                         = resWeight
                         | otherwise = 0

    isEvald val          = valueIsHNF env val

    isCase (Case {})     = True
    isCase _             = False

    real `times` int     = ceiling (real * fromIntegral int)
