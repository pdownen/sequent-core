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
import Language.SequentCore.Util

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
import OccurAnal   ( occurAnalysePgm )
import Outputable
import Type        ( mkFunTy )
import Var
import VarEnv
import VarSet

import Control.Applicative ( (<$>), (<*>) )
import Control.Exception   ( assert )
import Control.Monad       ( when )
import Data.Maybe

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
    binds' <- snd <$> simplBinds (initialEnv dflags) binds TopLevel
    freeTick SimplifierDone
    return binds'

simplCommand :: SimplEnv -> InCommand -> SimplM OutCommand
simplCommand env (Command { cmdLet = binds, cmdValue = val, cmdCont = cont })
  = do
    (env', binds') <- simplBinds env binds NotTopLevel
    cmd' <- simplCut env' val (staticPart env') cont
    return $ addLets binds' cmd'

simplValue :: SimplEnv -> InValue -> SimplM OutValue
simplValue env v
  = mkCompute <$> simplCut env' v (staticPart env') Return
  where env' = zapCont env

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

simplNonRec :: SimplEnv -> InVar -> StaticEnv -> InValue -> TopLevelFlag
            -> SimplM (SimplEnv, Maybe OutBind)
simplNonRec env_x x env_v v level
  | isTyVar x
  , Type ty <- assert (isTypeValue v) $ v
  = let ty'  = substTyStatic env_v ty
        tvs' = extendVarEnv (se_tvSubst env_x) x ty'
    in return (env_x { se_tvSubst = tvs' }, Nothing)
  | isCoVar x
  , Coercion co <- assert (isCoValue v) $ v
  = let co'  = substCoStatic env_v co
        cvs' = extendVarEnv (se_cvSubst env_x) x co'
    in return (env_x { se_cvSubst = cvs' }, Nothing)
  | otherwise
  = do
    preInline <- preInlineUnconditionally env_x x env_v v level
    if preInline
      then do
        tick (PreInlineUnconditionally x)
        let rhs = mkSuspension env_v v
            env' = extendIdSubst env_x x rhs
        return (env', Nothing)
      else do
        let (env', x') = enterScope env_x x
        v' <- simplValue (env' `setStaticPart` env_v) v
        (env'', maybeNewPair) <- completeBind env' x x' v' level
        return (env'', uncurry NonRec <$> maybeNewPair)

completeBind :: SimplEnv -> InVar -> OutVar -> OutValue -> TopLevelFlag
             -> SimplM (SimplEnv, Maybe (OutVar, OutValue))
completeBind env x x' v level
  = do
    postInline <- postInlineUnconditionally env x v level
    if postInline
      then do
        tick (PostInlineUnconditionally x)
        -- Nevermind about substituting x' for x; we'll substitute v instead
        let env' = extendIdSubst env x (DoneVal v)
        return (env', Nothing)
      else do
        -- TODO Eta-expansion goes here
        dflags <- getDynFlags
        let ins   = se_inScope env
            defs  = se_defs env
            x''   = x' `setIdInfo` idInfo x
            ins'  = extendInScopeSet ins x''
            defs' = extendVarEnv defs x'' (mkBoundTo dflags v (idOccInfo x'') level)
        return (env { se_inScope = ins', se_defs = defs' }, Just (x'', v))

simplRec :: SimplEnv -> StaticEnv -> [(InVar, InValue)] -> TopLevelFlag
         -> SimplM (SimplEnv, [(OutVar, OutValue)])
simplRec env_x env_v xvs level
  = go env0_x [ (x, x', v) | (x, v) <- xvs | x' <- xs' ] []
  where
    go env_x [] acc = return (env_x, reverse acc)
    go env_x ((x, x', v) : triples) acc
      = do
        preInline <- preInlineUnconditionally env_x x env_v v level
        if preInline
          then do
            tick (PreInlineUnconditionally x)
            let rhs  = mkSuspension env_v v
                env' = extendIdSubst env_x x rhs
            go env' triples acc
          else do
            v' <- simplValue (env_x `setStaticPart` env_v) v
            (env', bind') <- completeBind env_x x x' v' level
            go env' triples (bind' `consMaybe` acc)

    (env0_x, xs') = enterScopes env_x (map fst xvs)

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
  = assert (isReturnCont cont) $
    let ty' = substTy env_v ty
    in return $ valueCommand (Type ty')
simplCut env (Coercion co) _env_k cont
  = assert (isReturnCont cont) $
    let co' = substCo env co
    in return $ valueCommand (Coercion co')
simplCut env (Cont k) _env_k cont
  = assert (isReturnCont cont) $ do
      k' <- simplCont env k
      return $ valueCommand (Cont k')
simplCut env_v (Lam x c) env_k (App arg cont)
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
    c' <- simplCommand (zapCont env_v') c
    simplContWith (env_v `setStaticPart` env_k) (Lam x' c') cont
simplCut env_v val env_k (Case x ty alts cont@Case {})
  = do
    tick (CaseOfCase x)
    let contTy = ty `mkFunTy` contOuterType ty cont
    contVar <- asContId <$> mkSysLocalM (fsLit "k") contTy
    (env_k', newBind) <- simplNonRec (env_v `setStaticPart` env_k)
                                     contVar env_k (Cont cont) NotTopLevel
    let env_v' = env_k' `setStaticPart` staticPart env_v
    comm <- simplCut env_v' val (staticPart env_k') (Case x ty alts $ Jump contVar)
    return $ addLets (maybeToList newBind) comm
simplCut env_v val env_k (Case x _ alts cont)
  | Just (pairs, body) <- matchCase env_v val alts
  = do
    tick (KnownBranch x)
    (env', binds) <- go (env_v `setStaticPart` env_k) ((x, val) : pairs) []
    comm <- simplCommand (env' `pushCont` cont) body
    return $ addLets binds comm
  where
    go env [] acc
      = return (env, reverse acc)
    go env ((x, v) : pairs) acc
      = do
        (env', maybe_xv') <- simplNonRec env x (staticPart env_v) v NotTopLevel
        go env' pairs (maybe_xv' `consMaybe` acc)
simplCut env_v (Var x) env_k cont
  = case substId env_v x of
      DoneId x'
        -> do
           val'_maybe <- callSiteInline env_v x cont
           case val'_maybe of
             Nothing
               -> simplContWith (env_v `setStaticPart` env_k) (Var x') cont
             Just val'
               -> simplCut (zapSubstEnvs env_v) val' env_k cont
      DoneVal v
        -> simplCut (zapSubstEnvs env_v) v env_k cont
      SuspVal stat v
        -> simplCut (env_v `setStaticPart` stat) v env_k cont
simplCut env_v val@(Lit _) env_k cont
  = simplContWith (env_v `setStaticPart` env_k) val cont
simplCut env_v (Cons ctor args) env_k cont
  = do
    args' <- mapM (simplValue env_v) args
    simplContWith (env_v `setStaticPart` env_k) (Cons ctor args') cont
simplCut env_v (Compute c) env_k cont
  = simplCommand (bindCont env_v env_k cont) c

-- TODO Somehow handle updating Definitions with NotAmong values?
matchCase :: SimplEnv -> InValue -> [InAlt]
          -> Maybe ([(InVar, InValue)], InCommand)
-- TODO First, handle variables with substitutions/unfoldings
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
  , Nothing <- matchCase env_v val alts
  = Just ([], body)
matchCase env_v val (_ : alts)
  = matchCase env_v val alts
matchCase _ _ []
  = Nothing

simplCont :: SimplEnv -> InCont -> SimplM OutCont
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
    go env (App arg cont) kc
      = do
        arg' <- simplValue env arg
        go env cont (kc . App arg')
    go env (Cast co cont) kc
      -- TODO Simplify coercions
      = go env cont (kc . Cast co)
    go env (Case x ty alts cont) kc
      -- TODO A whole lot - cases are important
      = doCase env'' x' ty' alts []
      where
        (env', cont') | Jump {} <- cont 
                      = (bindCont env (staticPart env) cont, Return)
                      | otherwise
                      = (env, cont)
        (env'', x')   = enterScope env' x
        ty'           = substTy env'' ty
        env_orig      = env

        doCase _env x ty [] alt_acc
          = go env_orig cont' (kc . Case x ty (reverse alt_acc))
        doCase env x ty (Alt con xs c : alts) alt_acc
          = do
            let (env', xs') = enterScopes env xs
            c' <- simplCommand env' c
            doCase env x ty alts (Alt con xs' c' : alt_acc)
    go env (Tick ti cont) kc
      = go env cont (kc . Tick ti)
    go env (Jump x) kc
      -- TODO Consider call-site inline
      = case substId env x of
          DoneId x'
            -> return $ kc (Jump x')
          DoneVal (Cont k)
            -> go (zapSubstEnvs env) k kc
          SuspVal stat (Cont k)
            -> go (env `setStaticPart` stat) k kc
          _
            -> error "jump to non-continuation"
    go env Return kc
      | Just (env', cont) <- restoreEnv env
      = go env' cont kc
      | otherwise
      = return $ kc Return

simplContWith :: SimplEnv -> OutValue -> InCont -> SimplM OutCommand
simplContWith env val cont
  = mkCommand [] val <$> simplCont env cont

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
               -> SimplM (Maybe InValue)
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
    argDiscs             = sum (map argDisc (zip args argWeights))
    argDisc (arg, w)     | isEvald arg = w
                         | otherwise   = 0
    resDisc              | length args > length argWeights || isCase cont'
                         = resWeight
                         | otherwise = 0

    isEvald (Var x)      = x `elemVarEnv` se_defs env
    isEvald (Compute {}) = False
    isEvald _            = True

    isCase (Case {})     = True
    isCase _             = False

    real `times` int     = ceiling (real * fromIntegral int)
