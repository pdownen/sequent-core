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

import Language.SequentCore.Pretty ({-ppr_binds_top-})
import Language.SequentCore.Simpl.Env
import Language.SequentCore.Simpl.Monad
import Language.SequentCore.Syntax
import Language.SequentCore.Translate
import Language.SequentCore.Util

import BasicTypes
import Coercion    ( isCoVar )
import CoreMonad   ( Plugin(..), SimplifierMode(..), Tick(..), CoreToDo(..),
                     CoreM, defaultPlugin, reinitializeGlobals, errorMsg,
                     isZeroSimplCount
                     --,putMsg, pprSimplCount
                   )
import CoreSyn     ( isRuntimeVar, isCheapUnfolding )
import CoreUnfold  ( smallEnoughToInline )
import DynFlags    ( gopt, GeneralFlag(..) )
import Id
import HscTypes    ( ModGuts(..) )
import OccurAnal   ( occurAnalysePgm )
import Outputable
import Var
import VarEnv
import VarSet

import Control.Applicative ( (<$>), (<*>) )
import Control.Exception   ( assert )
import Data.Maybe

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
        -- putMsg  $ text "BEFORE" <+> int n
        --        $$ text "--------" $$ ppr_binds_top binds
        (binds', count) <- runSimplM globalEnv $ simplModule binds
        -- putMsg  $ text "AFTER" <+> int n
        --        $$ text "-------" $$ ppr_binds_top binds'
        let coreBinds' = bindsToCore binds'
            guts'      = guts { mg_binds = coreBinds' }
        if isZeroSimplCount count
          then do
            -- putMsg $ text "Done after" <+> int n <+> text "iterations"
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
  = snd <$> simplBinds initialEnv binds TopLevel

simplCommand :: SimplEnv -> InCommand -> SimplM OutCommand
simplCommand env (Command { cmdLet = binds, cmdValue = val, cmdCont = cont })
  = do
    (env', binds') <- simplBinds env binds NotTopLevel
    cmd' <- simplCut env' val (staticPart env') cont
    return $ addLets binds' cmd'

-- Simplifies a command that's standing in for a value, in other words a
-- mu-abstraction.
-- TODO Figure out how to explain this without reference to sequent calculus.
-- Otherwise, convince people that keeping mu-abstractions in sequent core
-- would be a win because the need for this would be self-evident.
simplStandaloneCommand :: SimplEnv -> InCommand -> SimplM OutCommand
simplStandaloneCommand env c = simplCommand (zapCont env) c

simplBinds :: SimplEnv -> [InBind] -> TopLevelFlag
           -> SimplM (SimplEnv, [OutBind])
simplBinds env [] _
  = return (env, [])
simplBinds env (b : bs) level
  = do
    (env', b') <- simplBind env (staticPart env) b level
    (env'', bs') <- simplBinds env' bs level
    return (env'', b' `consMaybe` bs')

simplBind :: SimplEnv -> StaticEnv -> InBind -> TopLevelFlag
          -> SimplM (SimplEnv, Maybe OutBind)
--simplBind env level bind
--  | pprTrace "simplBind" (text "Binding" <+> parens (ppr level) <> colon <+>
--                          ppr bind) False
--  = undefined
simplBind env_x env_c (NonRec x c) level
  = simplNonRec env_x x env_c c level
simplBind env_x env_c (Rec xcs) level
  = do
    (env', xcs') <- simplRec env_x env_c xcs level
    return (env', if null xcs' then Nothing else Just $ Rec xcs')

simplNonRec :: SimplEnv -> InVar -> StaticEnv -> InCommand -> TopLevelFlag
            -> SimplM (SimplEnv, Maybe OutBind)
simplNonRec env_x x env_c c level
  | isTyVar x
  , Type ty <- assert (isTypeArg c) $ cmdValue c
  = let ty'  = substTyStatic env_c ty
        tvs' = extendVarEnv (se_tvSubst env_x) x ty'
    in return (env_x { se_tvSubst = tvs' }, Nothing)
  | isCoVar x
  , Coercion co <- assert (isCoArg c) $ cmdValue c
  = let co'  = substCoStatic env_c co
        cvs' = extendVarEnv (se_cvSubst env_x) x co'
    in return (env_x { se_cvSubst = cvs' }, Nothing)
  | otherwise
  = do
    preInline <- preInlineUnconditionally env_x x env_c c level
    if preInline
      then do
        tick (PreInlineUnconditionally x)
        let rhs = mkSuspension env_c c
            env' = extendIdSubst env_x x rhs
        return (env', Nothing)
      else do
        let (env', x') = enterScope env_x x
        c' <- simplStandaloneCommand (env' `setStaticPart` env_c) c
        (env'', maybeNewPair) <- completeBind env' x x' c' level
        return (env'', uncurry NonRec <$> maybeNewPair)

completeBind :: SimplEnv -> InVar -> OutVar -> OutCommand -> TopLevelFlag
             -> SimplM (SimplEnv, Maybe (OutVar, OutCommand))
completeBind env x x' c level
  = do
    postInline <- postInlineUnconditionally env x c level
    if postInline
      then do
        tick (PostInlineUnconditionally x)
        -- Nevermind about substituting x' for x; we'll substitute c instead
        let env' = extendIdSubst env x (DoneComm c)
        return (env', Nothing)
      else do
        -- TODO Eta-expansion goes here
        let ins   = se_inScope env
            defs  = se_defs env
            x''   = x' `setIdInfo` idInfo x
            ins'  = extendInScopeSet ins x''
            defs' = extendVarEnv defs x'' (BoundTo c level)
        return (env { se_inScope = ins', se_defs = defs' }, Just (x'', c))

simplRec :: SimplEnv -> StaticEnv -> [(InVar, InCommand)] -> TopLevelFlag
         -> SimplM (SimplEnv, [(OutVar, OutCommand)])
simplRec env_x env_c xcs level
  = go env0_x [ (x, x', c) | (x, c) <- xcs | x' <- xs' ] []
  where
    go env_x [] acc = return (env_x, reverse acc)
    go env_x ((x, x', c) : triples) acc
      = do
        preInline <- preInlineUnconditionally env_x x env_c c level
        if preInline
          then do
            tick (PreInlineUnconditionally x)
            let rhs = mkSuspension env_c c
                env' = extendIdSubst env_x x rhs
            go env' triples acc
          else do
            c' <- simplStandaloneCommand (env_x `setStaticPart` env_c) c
            (env', bind') <- completeBind env_x x x' c' level
            go env' triples (bind' `consMaybe` acc)

    (env0_x, xs') = enterScopes env_x (map fst xcs)

-- TODO Deal with casts, i.e. implement the congruence rules from the
-- System FC paper
simplCut :: SimplEnv -> InValue -> StaticEnv -> InCont -> SimplM OutCommand
{-
simplCut env_v v env_k cont
  | pprTrace "simplCut" (
      ppr env_v $$ ppr v $$ ppr env_k $$ ppr cont
    ) False
  = undefined
-}
simplCut env_v (Type ty) _env_k cont
  = assert (null cont) $
    let ty' = substTy env_v ty
    in return $ valueCommand (Type ty')
simplCut env (Coercion co) _env_k cont
  = assert (null cont) $
    let co' = substCo env co
    in return $ valueCommand (Coercion co')
simplCut env_v (Var x) env_k cont
  = case substId env_v x of
      DoneId x'
        -> simplCont env'_k (Var x') cont
      DoneComm c
        -> simplCommand (suspendAndZapEnv env'_k cont) c
      SuspComm stat c
        -> simplCommand (suspendAndSetEnv env'_k stat cont) c
    where env'_k = env_v `setStaticPart` env_k
simplCut env_v (Lam x c) env_k (App arg : cont)
  = do
    tick (BetaReduction x)
    (env_v', newBind) <- simplNonRec env_v x env_k arg NotTopLevel
    -- Effectively, here we bind the covariable in the lambda to the current
    -- continuation before proceeding
    c' <- simplCommand (bindCont env_v' env_k cont) c
    return $ addLets (maybeToList newBind) c'
simplCut env_v (Lam x c) env_k cont
  = do
    let (env_v', x') = enterScope env_v x
    -- Simplify with an empty outer context
    -- (effectively, we enter a new scope for the covariable)
    c' <- simplStandaloneCommand env_v' c
    simplCont (env_v `setStaticPart` env_k) (Lam x' c') cont
simplCut env_v val env_k (Case x _ alts : cont)
  | Just (pairs, body) <- matchCase env_v val alts
  = do
    tick (KnownBranch x)
    (env', binds) <- go (env_v `setStaticPart` env_k)
                         ((x, valueCommand val) : pairs) []
    comm <- simplCommand env' (body `extendCont` cont)
    return $ addLets binds comm
  where
    go env [] acc
      = return (env, reverse (catMaybes acc))
    go env ((x, c) : pairs) acc
      = do
        (env', maybe_xc') <- simplNonRec env x (staticPart env_v) c NotTopLevel
        go env' pairs (maybe_xc' : acc)
simplCut env_v val@(Lit _) env_k cont
  = simplCont (env_v `setStaticPart` env_k) val cont
simplCut env_v (Cons ctor args) env_k cont
  = do
    args' <- mapM (simplCommand env_v) args
    simplCont (env_v `setStaticPart` env_k) (Cons ctor args') cont

-- TODO Somehow handle updating Definitions with NotAmong values?
matchCase :: SimplEnv -> InValue -> [InAlt]
          -> Maybe ([(InVar, InCommand)], InCommand)
-- TODO First, handle variables with substitutions/unfoldings
matchCase _env_v (Lit lit) (Alt (LitAlt lit') xs body : _alts)
  | assert (null xs) True
  , lit == lit'
  = Just ([], body)
matchCase _env_v (Cons ctor args) (Alt (DataAlt ctor') xs body : _alts)
  | assert (length args == length xs) True
  , ctor == ctor'
  = Just (zip xs args, body)
matchCase env_v val (Alt DEFAULT xs body : alts)
  | assert (null xs) True
  , Nothing <- matchCase env_v val alts
  = Just ([], body)
matchCase env_v val (_ : alts)
  = matchCase env_v val alts
matchCase _ _ []
  = Nothing

simplCont :: SimplEnv -> OutValue -> InCont -> SimplM OutCommand
{-
simplCont env val cont
  | pprTrace "simplCont" (
      ppr env $$ ppr val $$ ppr cont
    ) False
  = undefined
-}
simplCont env val cont
  = go env val cont []
  where
    go env val (App arg : cont) acc
      = do
        arg' <- simplStandaloneCommand env arg
        go env val cont (App arg' : acc)
    go env val (f@(Cast _) : cont) acc
      -- TODO Simplify coercions
      = go env val cont (f : acc)
    go env val (Case x ty alts : cont) acc
      -- TODO A whole lot - cases are important
      = let (env', x') = enterScope env x
            ty' = substTy env' ty
        in doCase env' x' ty' alts []
      where
        doCase env x ty [] alt_acc
          = go env val cont (Case x ty (reverse alt_acc) : acc)
        doCase env x ty (Alt con xs c : alts) alt_acc
          = do
            let (env', xs') = enterScopes env xs
            c' <- simplCommand env' c
            doCase env x ty alts (Alt con xs' c' : alt_acc)
    go env val (f@(Tick _) : cont) acc
      = go env val cont (f : acc)
    go env val [] acc
      | Just (env', cont) <- restoreEnv env
      = go env' val cont acc
      | otherwise
      = return $ Command { cmdLet = [], cmdValue = val, cmdCont = reverse acc }
  
-- Based on preInlineUnconditionally in SimplUtils; see comments there
preInlineUnconditionally :: SimplEnv -> InVar -> StaticEnv -> InCommand
                         -> TopLevelFlag -> SimplM Bool
-- preInlineUnconditionally _ _ _ _ _ = return False
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
          | otherwise = intCxt && canInlineInLam rhs
        canInlineInLam c
          | Just v <- asValueCommand c  = canInlineValInLam v
          | otherwise                   = False
        canInlineValInLam (Lit _)       = True
        canInlineValInLam (Lam x c)     = isRuntimeVar x || canInlineInLam c
        canInlineValInLam _             = False
        early_phase = case sm_phase mode of
                        Phase 0 -> False
                        _       -> True

-- Based on postInlineUnconditionally in SimplUtils; see comments there
postInlineUnconditionally :: SimplEnv -> OutVar -> OutCommand -> TopLevelFlag
                          -> SimplM Bool
postInlineUnconditionally _env x c level
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
      | isTrivial c                 = True
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

