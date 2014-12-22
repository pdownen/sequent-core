{-# LANGUAGE ParallelListComp #-}

module Language.SequentCore.Simpl (plugin) where

import Language.SequentCore.Ops
import Language.SequentCore.Pretty
import Language.SequentCore.Simpl.Env
import Language.SequentCore.Simpl.Monad
import Language.SequentCore.Syntax

import BasicTypes
import Coercion    ( isCoVar )
import CoreMonad   ( Plugin(..), SimplifierMode(..), Tick(..), CoreToDo(..),
                     CoreM, defaultPlugin, reinitializeGlobals, putMsg, errorMsg,
                     isZeroSimplCount )
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
        putMsg  $ text "BEFORE" <+> int n
               $$ text "--------" $$ ppr_binds_top binds
        (binds', count) <- runSimplM globalEnv $ simplModule binds
        putMsg  $ text "AFTER" <+> int n
               $$ text "-------" $$ ppr_binds_top binds'
        let coreBinds' = bindsToCore binds'
            guts'      = guts { mg_binds = coreBinds' }
        if isZeroSimplCount count
          then do
            putMsg $ text "Done after" <+> int n <+> text "iterations"
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
  = snd <$> simplBinds initialEnv TopLevel binds

simplCommand :: SimplEnv -> InCommand -> SimplM OutCommand
simplCommand env (Command { cmdLet = binds, cmdValue = val, cmdCont = cont })
  = do
    (env', binds') <- simplBinds env NotTopLevel binds
    cmd' <- simplCut env' val env' cont
    return $ addLets binds' cmd'

simplBinds :: SimplEnv -> TopLevelFlag -> [InBind]
           -> SimplM (SimplEnv, [OutBind])
simplBinds env _ []
  = return (env, [])
simplBinds env level (b : bs)
  = do
    (env', b') <- simplBind env level b
    (env'', bs') <- simplBinds env' level bs
    return (env'', maybeToList b' ++ bs')

simplBind :: SimplEnv -> TopLevelFlag -> InBind
          -> SimplM (SimplEnv, Maybe OutBind)
--simplBind env level bind
--  | pprTrace "simplBind" (text "Binding" <+> parens (ppr level) <> colon <+>
--                          ppr bind) False
--  = undefined
simplBind env level (NonRec x c)
  = do
    (env', x'c') <- simplNonRec env level x c
    return (env', uncurry NonRec <$> x'c')
simplBind env level (Rec xcs)
  = do
    (env', xcs') <- simplRec env level xcs
    return (env', if null xcs' then Nothing else Just (Rec xcs'))

simplNonRec :: SimplEnv -> TopLevelFlag -> InVar -> InCommand
            -> SimplM (SimplEnv, Maybe (OutVar, OutCommand))
simplNonRec env level x c
  | isTyVar x
  , Type ty <- assert (isTypeArg c) $ cmdValue c
  = let ty'   = substTy env ty
        tvs' = extendVarEnv (se_tvSubst env) x ty'
    in return (env { se_tvSubst = tvs' }, Nothing)
  | isCoVar x
  , Coercion co <- assert (isCoArg c) $ cmdValue c
  = let co'  = substCo env co
        cvs' = extendVarEnv (se_cvSubst env) x co'
    in return (env { se_cvSubst = cvs' }, Nothing)
  | otherwise
  = do
    preInline <- preInlineUnconditionally env level x c
    if preInline
      then do
        tick (PreInlineUnconditionally x)
        let rhs = mkSuspension env c
            env' = extendIdSubst env x rhs
        return (env', Nothing)
      else do
        let (env', x') = enterScope env x
        c' <- simplCommand env' c
        completeBind env' level x x' c'

completeBind :: SimplEnv -> TopLevelFlag -> InVar -> OutVar -> OutCommand
             -> SimplM (SimplEnv, Maybe (OutVar, OutCommand))
completeBind env level x x' c
  = do
    postInline <- postInlineUnconditionally env level x c
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

simplRec :: SimplEnv -> TopLevelFlag -> [(InVar, InCommand)]
         -> SimplM (SimplEnv, [(OutVar, OutCommand)])
simplRec env level xcs
  = go env0 [ (x, x', c) | (x, c) <- xcs | x' <- xs' ] []
  where
    go env [] acc = return (env, reverse acc)
    go env ((x, x', c) : triples) acc
      = do
        preInline <- preInlineUnconditionally env level x c
        if preInline
          then do
            tick (PreInlineUnconditionally x)
            let rhs = mkSuspension env c
                env' = extendIdSubst env x rhs
            go env' triples acc
          else do
            c' <- simplCommand env c
            (env', bind') <- completeBind env level x x' c'
            go env' triples (maybeToList bind' ++ acc)

    (env0, xs') = enterScopes env (map fst xcs)

-- TODO Lots of things this function should do:
-- * Beta-reduction
-- * Case-reduction
-- * Optimize the continuation wrt casts 
simplCut :: SimplEnv -> InValue -> SimplEnv -> InCont -> SimplM OutCommand
simplCut _env_v val@(Lit _) env_k cont
  = simplCont env_k val cont
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
        -> simplCont env_k (Var x') cont
      DoneComm c
        -> simplCommand (suspendAndZapEnv env_k cont) c
      SuspComm ids tvs cvs c
        -> simplCommand (suspendAndSetEnv env_k ids tvs cvs cont) c
simplCut env_v (Lam x c) env_k cont
  = do
    let (env_v', x') = enterScope env_v x
    c' <- simplCommand env_v' c
    simplCont env_k (Lam x' c') cont

simplCont :: SimplEnv -> OutValue -> InCont -> SimplM OutCommand
simplCont env val cont
  = go env val cont []
  where
    go env val (App arg : cont) acc
      = do
        arg' <- simplCommand env arg
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
preInlineUnconditionally :: SimplEnv -> TopLevelFlag -> InVar -> InCommand
                         -> SimplM Bool
preInlineUnconditionally _env level x rhs
  = do
    ans <- go <$> getMode <*> getDynFlags
    pprTrace "preInlineUnconditionally" (ppr x <> colon <+> text (show ans)) $
      return ans
  where
    go mode dflags
      | not active                              = False
      | not enabled                             = False
      | TopLevel <- level, isBottomingId x      = False
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
postInlineUnconditionally :: SimplEnv -> TopLevelFlag -> OutVar -> OutCommand
                          -> SimplM Bool
postInlineUnconditionally _env level x c
  = go <$> getMode <*> getDynFlags
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

