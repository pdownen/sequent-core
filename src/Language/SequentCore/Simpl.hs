{-# LANGUAGE ParallelListComp, TupleSections #-}

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
import Language.SequentCore.Pretty (pprTopLevelBinds)
import Language.SequentCore.Simpl.Env
import Language.SequentCore.Simpl.Monad
import Language.SequentCore.Syntax
import Language.SequentCore.Translate
import Language.SequentCore.Util

import BasicTypes
import Coercion    ( Coercion, isCoVar )
import CoreMonad   ( Plugin(..), SimplifierMode(..), Tick(..), CoreToDo(..),
                     CoreM, defaultPlugin, reinitializeGlobals,
                     isZeroSimplCount, pprSimplCount, putMsg, errorMsg
                   )
import CoreSyn     ( isRuntimeVar, isCheapUnfolding )
import CoreUnfold  ( smallEnoughToInline )
import DataCon
import DynFlags    ( gopt, GeneralFlag(..), ufKeenessFactor, ufUseThreshold )
import FastString
import Id
import HscTypes    ( ModGuts(..) )
import Literal     ( Literal )
import OccurAnal   ( occurAnalysePgm )
import Outputable
import Type        ( Type, isUnLiftedType )
import Var
import VarEnv
import VarSet

import Control.Applicative ( (<$>), (<*>) )
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
            binds     = fromCoreModule occBinds
        when linting $ case lintCoreBindings binds of
          Just err -> pprPgmError "Sequent Core Lint error (pre-simpl)"
            (withPprStyle defaultUserStyle $ err $$ pprTopLevelBinds binds $$ vcat (map ppr occBinds))
          Nothing -> return ()
        when dumping $ putMsg  $ text "BEFORE" <+> int n
                              $$ text "--------" $$ pprTopLevelBinds binds
        (binds', count) <- runSimplM globalEnv $ simplModule binds
        when linting $ case lintCoreBindings binds' of
          Just err -> pprPanic "Sequent Core Lint error"
            (withPprStyle defaultUserStyle $ err $$ pprTopLevelBinds binds')
          Nothing -> return ()
        when dumping $ putMsg  $ text "AFTER" <+> int n
                              $$ text "-------" $$ pprTopLevelBinds binds'
        let coreBinds' = bindsToCore binds'
            guts'      = guts { mg_binds = coreBinds' }
        when dumping $ putMsg  $ text "SUMMARY" <+> int n
                              $$ text "---------" $$ pprSimplCount count
                              $$ text "CORE AFTER" <+> int n
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
simplCommand env (Command { cmdLet = binds, cmdTerm = term, cmdKont = kont })
  = do
    env' <- simplBinds env binds NotTopLevel
    simplCut env' term (staticPart env') kont

simplTermNoFloats :: SimplEnv -> InTerm -> SimplM OutTerm
simplTermNoFloats env term
  = do
    (env', term') <- simplTerm (zapFloats env) term
    wrapFloatsAroundTerm env' term'

simplTerm :: SimplEnv -> InTerm -> SimplM (SimplEnv, OutTerm)
simplTerm _env (Kont {})
  = panic "simplTerm"
simplTerm env (Type ty)
  = return (env, Type (substTy env ty))
simplTerm env (Coercion co)
  = return (env, Coercion (substCo env co))
simplTerm env (Compute k comm)
  = do
    let (env', k') = enterScope env k
    comm' <- simplCommandNoFloats (setKont env' k) comm
    return (env, mkCompute k' comm')
simplTerm env v
  = do
    (env', k) <- mkFreshKontId env (fsLit "*termk") ty
    let env'' = zapFloats $ setKont env' k
    (env''', comm) <- simplCut env'' v (staticPart env'') (Return k)
    return (env, mkCompute k (wrapFloats env''' comm))
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
simplBind env (NonRec x v) level
  = simplNonRec env x (staticPart env) v level
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
simplLazyBind env_x x x' env_v v level isRec
  | tracing
  , pprTraceShort "simplLazyBind" ((if x == x' then ppr x else ppr x <+> darrow <+> ppr x')
                                      <+> ppr level <+> ppr isRec $$ ppr v) False
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
    preInline <- preInlineUnconditionally env_x x env_v v level
    if preInline
      then do
        tick (PreInlineUnconditionally x)
        let rhs = mkSuspension env_v v
            env' = extendIdSubst env_x x rhs
        return env'
      else case v of
        Kont kont
          | TopLevel <- level
          -> pprPanic "simplLazyBind: top-level cont" (ppr x)
          | otherwise
          -> do
             let env_v' = zapFloats (env_v `inDynamicScope` env_x)
             (env_v'', split) <- splitDupableKont env_v' kont
             case split of
               DupeAll dup -> do
                 -- TODO We can't tick here because often this is simply canceling
                 -- a continuation parameter that we added, say, to simplify a
                 -- term. But it seems like we *should* be ticking here sometimes?
                 -- tick (PostInlineUnconditionally x)
                 return $ extendIdSubst (env_x `addFloats` env_v'') x (DoneTerm (Kont dup))
               DupeNone -> do
                 (env_v''', kont') <- simplKont env_v'' kont
                 finish x x' env_v''' (Kont kont')
               DupeSome dupk nodup -> do
                 (env_v''', nodup') <- simplKont (zapFloats env_v'') nodup
                 (env_v'''', nodup_x) <-
                   mkFreshKontId env_v''' (fsLit "*nodup") (kontType nodup')
                 env_x' <- finish nodup_x nodup_x env_v'''' (Kont nodup')
                 tick (PostInlineUnconditionally x)
                 -- Trickily, nodup may have been duped after all if it's
                 -- post-inlined. Thus assemble dup from the final value of
                 -- nodup.
                 (env_x'', value_nodup_x) <- simplKont env_x' (Return nodup_x)
                 let dup = dupk value_nodup_x
                     env_x''' = env_x'' `addFloats` env_v''
                 return $ extendIdSubst env_x''' x (DoneTerm (Kont dup))
        _ -> do
             -- TODO Handle floating type lambdas
             let env_v' = zapFloats (env_v `inDynamicScope` env_x)
             (env_v'', v') <- simplTerm env_v' v
             -- TODO Something like Simplify.prepareRhs
             finish x x' env_v'' v'
  where
    finish new_x new_x' env_v' v'
      = do
        (env_x', v'')
          <- if not (doFloatFromRhs level isRec False v' env_v')
                then do v'' <- wrapFloatsAroundTerm env_v' v'
                        return (env_x, v'')
                else do tick LetFloatFromLet
                        return (env_x `addFloats` env_v', v')
        completeBind env_x' new_x new_x' v'' level

wrapFloatsAroundKont :: SimplEnv -> OutKont -> SimplM OutKont
wrapFloatsAroundKont env kont
  | isEmptyFloats env
  = return kont
  | otherwise
  -- Remember, most nontrivial continuations are strict contexts. Therefore it's
  -- okay to rewrite
  --   E ==> case of [ a -> <a | E> ]
  --  *except* when E is a Return or (less commonly) some Casts or Ticks before a
  -- Return. However, we only call this when something's being floated from a
  -- continuation, and it seems unlikely we'd be floating a let from a Return.
  = do
    let ty = kontType kont
    (env', x) <- mkFreshVar env (fsLit "$in") ty
    let comm = wrapFloats env' (mkCommand [] (Var x) kont)
    return $ Case x [Alt DEFAULT [] comm]
    
wrapFloatsAroundTerm :: SimplEnv -> OutTerm -> SimplM OutTerm
wrapFloatsAroundTerm env (Kont kont)
  = Kont <$> wrapFloatsAroundKont env kont
wrapFloatsAroundTerm env term
  | isEmptyFloats env
  = return term
  | not (isProperTerm term)
  = pprPanic "wrapFloatsAroundTerm" (ppr term)
  | otherwise
  = do
    let ty = termType term
    (env', k) <- mkFreshKontId env (fsLit "*wrap") ty
    return $ mkCompute k $ wrapFloats env' (mkCommand [] term (Return k))

completeNonRec :: SimplEnv -> InVar -> OutVar -> OutTerm -> TopLevelFlag
                           -> SimplM SimplEnv
-- TODO Something like Simplify.prepareRhs
completeNonRec = completeBind

completeBind :: SimplEnv -> InVar -> OutVar -> OutTerm -> TopLevelFlag
             -> SimplM SimplEnv
completeBind env x x' v level
  = do
    postInline <- postInlineUnconditionally env x v level
    if postInline
      then do
        tick (PostInlineUnconditionally x)
        -- Nevermind about substituting x' for x; we'll substitute v instead
        return $ extendIdSubst env x (DoneTerm v)
      else do
        -- TODO Eta-expansion goes here
        dflags <- getDynFlags
        let x''   = x' `setIdInfo` idInfo x
            -- FIXME Be smarter about this! Sometimes we want a BoundToDFun!
            -- Currently this is causing a lot of dictionaries to fail to inline
            -- at obviously desirable times.
            -- See simplUnfolding in Simplify
            def   = mkBoundTo dflags v level
            (env', x''') = setDef env x'' def
        when tracing $ liftCoreM $ putMsg (text "defined" <+> ppr x''' <+> equals <+> ppr def)
        return $ addNonRecFloat env' x''' v

simplRec :: SimplEnv -> [(InVar, InTerm)] -> TopLevelFlag
         -> SimplM SimplEnv
simplRec env xvs level
  = do
    let (env', xs') = enterScopes env (map fst xvs)
    env'' <- foldM doBinding (zapFloats env')
               [ (x, x', v) | (x, v) <- xvs | x' <- xs' ]
    return $ env' `addRecFloats` env''
  where
    doBinding :: SimplEnv -> (InId, OutId, InTerm) -> SimplM SimplEnv
    doBinding env' (x, x', v)
      = simplLazyBind env' x x' (staticPart env') v level Recursive

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
simplCut env_v (Var x) env_k kont
  = case substId env_v x of
      DoneId x'
        -> do
           term'_maybe <- callSiteInline env_v x' kont
           case term'_maybe of
             Nothing
               -> simplCut2 env_v (Var x') env_k kont
             Just term'
               -> do
                  tick (UnfoldingDone x')
                  simplCut (zapSubstEnvs env_v) term' env_k kont
      DoneTerm v
        -- Term already simplified (then PostInlineUnconditionally'd), so
        -- don't do any substitutions when processing it again
        -> simplCut2 (zapSubstEnvs env_v) v env_k kont
      SuspTerm stat v
        -> simplCut (env_v `setStaticPart` stat) v env_k kont
simplCut env_v term env_k kont
  -- Proceed to phase 2
  = simplCut2 env_v term env_k kont

-- Second phase of simplCut. Now, if the term is a variable, we looked it up
-- and substituted it but decided not to inline it. (In other words, if it's an
-- id, it's an OutId.)
simplCut2 :: SimplEnv -> OutTerm -> StaticEnv -> InKont
                      -> SimplM (SimplEnv, OutCommand)
simplCut2 env_v (Type ty) _env_k kont
  = assert (isReturnKont kont) $
    let ty' = substTy env_v ty
    in return (env_v, Command [] (Type ty') kont)
simplCut2 env_v (Coercion co) _env_k kont
  = assert (isReturnKont kont) $
    let co' = substCo env_v co
    in return (env_v, Command [] (Coercion co') kont)
simplCut2 _env_v (Kont {}) _env_k kont
  = pprPanic "simplCut of cont" (ppr kont)
simplCut2 env_v (Lam x body) env_k (App arg kont)
  = do
    tick (BetaReduction x)
    env_v' <- simplNonRec env_v x env_k arg NotTopLevel
    simplCut env_v' body env_k kont
simplCut2 env_v (Lam x body) env_k kont
  = do
    let (env_v', x') = enterScope env_v x
    body' <- simplTermNoFloats env_v' body
    simplKontWith (env_v' `setStaticPart` env_k) (Lam x' body') kont
simplCut2 env_v term env_k kont
  | Just (value, kont') <- splitValue term kont
  , Just (env_k', x, alts) <- kontIsCase_maybe (env_v `setStaticPart` env_k) kont'
  , Just (pairs, body) <- matchCase env_v value alts
  = do
    tick (KnownBranch x)
    env' <- foldM doPair (env_v `setStaticPart` env_k') ((x, valueToTerm value) : pairs)
    simplCommand env' body
  where
    doPair env (x, v)
      = simplNonRec env x (staticPart env_v) v NotTopLevel

-- Adapted from Simplify.rebuildCase (clause 2)
-- See [Case elimination] in Simplify
simplCut2 env_v term env_k (Case case_bndr [Alt _ bndrs rhs])
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
    case_bndr_evald_next (Command [] (Var v) _) = v == case_bndr
    case_bndr_evald_next _                      = False
      -- Could allow for let bindings,
      -- but the original code in Simplify suggests doing so would be expensive

simplCut2 env_v (Compute k c) env_k kont
  = do
    env_v' <- simplNonRec env_v k env_k (Kont kont) NotTopLevel
    simplCommand env_v' c
simplCut2 env_v term@(Lit {}) env_k kont
  = simplKontWith (env_v `setStaticPart` env_k) term kont
simplCut2 env_v term@(Var {}) env_k kont
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

simplKontNoFloats :: SimplEnv -> InKont -> SimplM OutKont
simplKontNoFloats env kont
  = do
    (env', kont') <- simplKont (zapFloats env) kont
    wrapFloatsAroundKont env' kont'

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
        let (env', x') = enterScope env x
        alts' <- forM alts $ \(Alt con xs c) -> do
          let (env'', xs') = enterScopes env' xs
          c' <- simplCommandNoFloats env'' c
          return $ Alt con xs' c'
        return (env, kc (Case x' alts'))
    go env (Tick ti kont) kc
      = go env kont (kc . Tick ti)
    go env (Return x) kc
      -- TODO Consider call-site inline
      = case substId env x of
          DoneId x'
            -> return (env, kc (Return x'))
          DoneTerm (Kont k)
            -> go (zapSubstEnvs env) k kc
          SuspTerm stat (Kont k)
            -> go (env `setStaticPart` stat) k kc
          _
            -> panic "return to non-continuation"

simplKontWith :: SimplEnv -> OutTerm -> InKont -> SimplM (SimplEnv, OutCommand)
simplKontWith env term kont
  = do
    (env', kont') <- simplKont env kont
    return (env', mkCommand [] term kont')

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
    DoneTerm v -> return v
    SuspTerm stat v -> simplTermNoFloats (env `setStaticPart` stat) v

simplKontId :: SimplEnv -> KontId -> SimplM OutKont
simplKontId env k
  | isKontId k
  = case substId env k of
      DoneId k'           -> return $ Return k'
      DoneTerm (Kont kont)-> return kont
      SuspTerm stat (Kont kont)
        -> simplKontNoFloats (env `setStaticPart` stat) kont
      other               -> pprPanic "simplKontId: bad kont binding"
                               (ppr k <+> arrow <+> ppr other)
  | otherwise
  = pprPanic "simplKontId: not a kont id" (ppr k)

-- Based on preInlineUnconditionally in SimplUtils; see comments there
preInlineUnconditionally :: SimplEnv -> InVar -> StaticEnv -> InTerm
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
          | otherwise = intCxt && canInlineTermInLam rhs
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
postInlineUnconditionally :: SimplEnv -> OutVar -> OutTerm -> TopLevelFlag
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
      | isTrivialTerm v             = True
      | otherwise
      = case occ_info of
          OneOcc in_lam _one_br int_cxt
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
  | termIsConstruction rhs, kontIsCase env kont
  = True
  | Lit {} <- rhs, kontIsCase env kont
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
    consider [] []         | kontIsCase env kont' = True -- (c) ditto
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
smallEnough env term (Usually unsatOk boringOk) kont
  = (unsatOk || not unsat) && (boringOk || not boring)
  where
    unsat = length valArgs < termArity term
    (_, valArgs, _) = collectTypeAndOtherArgs kont
    boring = isReturnKont kont && not (kontIsCase env kont)
    -- FIXME Should probably count known applications as interesting, too

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
inlineDFun env bndrs con conArgs kont
--  | pprTraceShort "inlineDFun" (sep ([ppr bndrs, ppr con, ppr conArgs, ppr kont, ppr args, ppr kont']) $$
--      if enoughArgs && kontIsCase env kont' then text "YES" else text "NO") False
--  = undefined
  | enoughArgs, kontIsCase env kont'
  = Just term
  | otherwise
  = Nothing
  where
    (args, kont') = collectArgsUpTo (length bndrs) kont
    enoughArgs    = length args == length bndrs
    term          = mkLambdas bndrs bodyTerm
    bodyTerm      = mkAppTerm (Var (dataConWorkId con)) conArgs

data KontSplitting
  = DupeAll OutKont
  | DupeNone
  | DupeSome (OutKont -> OutKont) InKont

-- | Divide a continuation into some (floated) bindings, a simplified
-- continuation we'll happily copy into many case branches, and possibly an
-- unsimplified continuation that we'll keep in a let binding and invoke from
-- each branch.
--
-- The rules:
--   1. Duplicate returns.
--   2. Duplicate casts.
--   3. Don't duplicate ticks (because GHC doesn't).
--   4. Duplicate applications, but ANF-ize them first to share the arguments.
--   5. Don't duplicate cases (!) because, unlike with Simplify.mkDupableCont,
--        we don't need to (see comment in Case clause).
--
-- TODO We could conceivably copy single-branch cases, since this would still
-- limit bloat, but we would need polyadic continuations in most cases (just as
-- GHC's join points can be polyadic). The simplest option would be to use
-- regular continuations of unboxed tuples for this, though that could make
-- inlining decisions trickier.

splitDupableKont :: SimplEnv -> InKont -> SimplM (SimplEnv, KontSplitting)
splitDupableKont env kont
  = do
    (env', ans) <- go env True (\kont' -> kont') kont
    return $ case ans of
      Left dup                 -> (env', DupeAll dup)
      Right (True,  _,  _)     -> (env', DupeNone)
      Right (False, kk, nodup) -> (env', DupeSome kk nodup)
  where
    -- The OutKont -> OutKont is a continuation for the outer continuation (!!).
    -- The Bool is there because we can't test whether the continuation is the
    -- identity.
    go :: SimplEnv -> Bool -> (OutKont -> OutKont) -> InKont
       -> SimplM (SimplEnv, Either OutKont (Bool, OutKont -> OutKont, InKont))
    go env top kk (Return kid)
      = case substId env kid of
          DoneId  kid'              -> return (env, Left $ kk (Return kid'))
          DoneTerm (Kont kont')     -> do
                                       let env' = zapFloats (zapSubstEnvs env)
                                       (env'', ans) <- go env' top kk kont'
                                       return (env `addFloats` env'', ans)
          SuspTerm stat (Kont kont')-> do
                                       let env' = zapFloats (stat `inDynamicScope` env)
                                       (env'', ans) <- go env' top kk kont'
                                       return (env `addFloats` env'', ans)
          other                     -> pprPanic "non-continuation at cont id"
                                         (ppr other)
    
    go env _top kk (Cast co kont)
      = do
        co' <- simplCoercion env co
        go env False (kk . Cast co') kont
    
    go env top kk kont@(Tick {})
      = return (env, Right (top, kk, kont))
    
    go env _top kk (App arg kont)
      = do
        (env', arg') <- makeTrivial env arg
        go env' False (kk . App arg') kont

    go env top kk kont@(Case {})
      -- Never duplicate cases! This is a marked departure from the original
      -- simplifier, which goes to great lengths to inline case statements in
      -- the hopes of making a case reduction possible. (For instance, this is
      -- the purpose of the case-of-case transform.) However, we are much better
      -- prepared than it is to detect known-branch conditions because we can
      -- easily check whether an id is bound to a case (much as GHC uses
      -- exprIsConApp_maybe to find whether one is bound to a constructor).
      = return (env, Right (top, kk, kont)) 

makeTrivial :: SimplEnv -> InTerm
                        -> SimplM (SimplEnv, OutTerm)
makeTrivial env term
  -- TODO Can't do this, since term is an InTerm and may need to be simplified.
  -- Maybe we should take an OutTerm instead?
  --  | isTrivialTerm term
  --  = return (env, term)
  --  | otherwise
  = do
    (env', bndr) <- case term of
      Kont kont -> mkFreshKontId env (fsLit "*trivk") (substTy env (kontType kont))
      _         -> mkFreshVar    env (fsLit "triv") (substTy env (termType term))
    env'' <- simplLazyBind env' bndr bndr (staticPart env') term NotTopLevel NonRecursive
    term_final <- simplVar env'' bndr
    return (env'', term_final)

kontIsCase :: SimplEnv -> InKont -> Bool
kontIsCase _env (Case {}) = True
kontIsCase env (Return k)
  | Just (BoundTo (Kont kont) _ _) <- lookupVarEnv (se_defs env) k
  = kontIsCase env kont
kontIsCase _ _ = False

kontIsCase_maybe :: SimplEnv -> InKont -> Maybe (StaticEnv, InId, [InAlt])
kontIsCase_maybe env (Case bndr alts) = Just (staticPart env, bndr, alts)
kontIsCase_maybe env (Return k)
  = case substId env k of
      DoneId k' ->
        case lookupVarEnv (se_defs env) k' of
          Just (BoundTo (Kont kont) _ _) -> kontIsCase_maybe (zapSubstEnvs env) kont
          _                              -> Nothing
      DoneTerm (Kont kont)               -> kontIsCase_maybe (zapSubstEnvs env) kont
      SuspTerm stat (Kont kont)          -> kontIsCase_maybe (stat `inDynamicScope` env) kont
      _                                  -> panic "kontIsCase_maybe"
kontIsCase_maybe _ _ = Nothing

-- TODO This might be generally useful; move to Syntax.hs?
data Value b
  = LitVal Literal
  | LamVal [b] (Term b)
  | ConsVal DataCon [Type] [Term b]
  
type SeqCoreValue = Value SeqCoreBndr
type InValue = SeqCoreValue
type OutValue = SeqCoreValue
  
splitValue :: Term b -> Kont b -> Maybe (Value b, Kont b)
splitValue (Lit lit) kont = Just (LitVal lit, kont)
splitValue term@(Lam {}) kont = Just (uncurry LamVal (lambdas term), kont)
splitValue (Var fid) kont
  | Just dc <- isDataConWorkId_maybe fid
  , length valArgs == dataConRepArity dc
  = Just (ConsVal dc tyArgs valArgs, kont')
  where
    (tyArgs, valArgs, kont') = collectTypeAndOtherArgs kont
splitValue _ _               = Nothing

valueToTerm :: SeqCoreValue -> SeqCoreTerm
valueToTerm (LitVal lit)          = Lit lit
valueToTerm (LamVal xs t)         = mkLambdas xs t
valueToTerm (ConsVal dc tys vals) = mkConstruction dc tys vals
