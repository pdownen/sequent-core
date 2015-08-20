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

import Language.SequentCore.Arity
import Language.SequentCore.Lint
import Language.SequentCore.OccurAnal
import Language.SequentCore.Pretty (pprTopLevelBinds)
import Language.SequentCore.Simpl.Env
import Language.SequentCore.Simpl.Monad
import Language.SequentCore.Simpl.Util
import Language.SequentCore.Syntax
import Language.SequentCore.Translate
import Language.SequentCore.Util
import Language.SequentCore.WiredIn

import BasicTypes
import Coercion    ( coercionKind, isCoVar, mkCoCast )
import CoreMonad   ( Plugin(..), SimplifierMode(..), Tick(..), CoreToDo(..),
                     CoreM, defaultPlugin, reinitializeGlobals,
                     isZeroSimplCount, pprSimplCount, simplCountN,
                     putMsg,
                     getRuleBase
                   )
import CoreSubst   ( deShadowBinds )
import CoreSyn     ( CoreVect(..), CoreRule(..)
                   , isRuntimeVar, isCheapUnfolding
                   , tickishCounts
                   , ruleArity )
import CoreUnfold  ( smallEnoughToInline )
import DataCon
import DynFlags    ( DynFlags, DumpFlag(..), GeneralFlag(..)
                   , gopt, dopt
                   , ufKeenessFactor, ufUseThreshold )
import ErrUtils    ( dumpSDoc )
import FastString
import Id
import IdInfo      ( IdInfo, demandInfo, strictnessInfo, vanillaIdInfo,
                     setArityInfo, setDemandInfo, setStrictnessInfo )
import HscTypes    ( ModGuts(..), VectInfo(..) )
import Literal     ( litIsDupable, litIsLifted )
import Maybes      ( whenIsJust )
import MkCore      ( mkWildValBinder )
import MonadUtils
import Name        ( mkSystemVarName )
import Outputable
import Pair
import qualified PprCore as Core
import Rules       ( extendRuleBaseList, lookupRule )
import Type        ( Type, applyTy, funResultTy, splitFunTy_maybe, splitForAllTy_maybe
                   , isUnLiftedType
                   , mkTyVarTy )
import TysWiredIn  ( mkTupleTy )
import UniqSupply
import Util        ( debugIsOn )
import Var
import VarEnv
import VarSet

import Control.Arrow       ( second )
import Control.Exception   ( assert )
import Control.Monad       ( foldM, forM, when )

import Data.Maybe          ( catMaybes, isJust, mapMaybe )

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
    = CoreDoPluginPass "SeqSimpl" (runSimplifier max mode)

runSimplifier :: Int -> SimplifierMode -> ModGuts -> CoreM ModGuts
runSimplifier iters mode guts
  = do
    when (tracing || dumping) $ putMsg  $ text "RUNNING SEQUENT CORE SIMPLIFIER"
                                       $$ text "Mode:" <+> ppr mode
    -- FIXME deShadowBinds is a crutch - type variable shadowing causes bugs
    let coreBinds = deShadowBinds (mg_binds guts)
        binds = fromCoreModule coreBinds
    when dumping $ putMsg  $ text "INITIAL CORE"
                          $$ text "------------"
                          $$ Core.pprCoreBindings coreBinds
    when (dumping && not (null rules)) $
      putMsg  $ text "CORE RULES"
             $$ text "----------"
             $$ ppr rules
    when linting $ do
      when dumping $ putMsg  $ text "LINT"
                            $$ text "----"
      runLint "pre-simpl" binds (text "--- Original Core: ---"
                                 $$ Core.pprCoreBindings coreBinds)
      when dumping $ putMsg $ text "LINT PASSED"
    binds' <- go 1 [] binds
    let coreBinds' = bindsToCore binds'
    when dumping $ putMsg  $ text "FINAL CORE"
                          $$ text "----------"
                          $$ Core.pprCoreBindings coreBinds'
    return $ guts { mg_binds = coreBinds' }
  where
    rules = mg_rules guts
    
    go n prevCounts binds
      | n > iters
      = (warnPprTrace (debugIsOn && iters > 2) __FILE__ __LINE__ $
          text "Simplifier bailing out after" <+> int iters
            <+> text "iterations"
            <+> (brackets $ hsep $ punctuate comma $
                 map (int . simplCountN) (reverse prevCounts)))
        return binds
      | otherwise
      = do
        dflags <- getDynFlags
        ruleBase <- getRuleBase
        let mod       = mg_module guts
            vectVars  = mkVarSet $
                          catMaybes [ fmap snd $ lookupVarEnv (vectInfoVar (mg_vect_info guts)) bndr
                                    | Vect bndr _ <- mg_vect_decls guts]
                          ++
                          catMaybes [ fmap snd $ lookupVarEnv (vectInfoVar (mg_vect_info guts)) bndr
                                    | bndr <- bindersOfBinds binds]
                                    -- FIXME: This second comprehensions is only needed as long as we
                                    --        have vectorised bindings where we get "Could NOT call
                                    --        vectorised from original version".
            (maybeVects, maybeVectVars)
                      = case sm_phase mode of
                          InitialPhase -> (mg_vect_decls guts, vectVars)
                          _            -> ([], vectVars)
            env = initialEnv dflags mode (ruleBase `extendRuleBaseList` rules)
            occBinds = runOccurAnal env mod maybeVects maybeVectVars binds
        when dumping $ putMsg  $ text "BEFORE" <+> int n
                              $$ text "--------" $$ pprTopLevelBinds occBinds
        runLint "in occurrence analysis" occBinds (text "--- Original Sequent Core: ---"
                                                   $$ pprTopLevelBinds binds)
        when linting $ whenIsJust (lintCoreBindings occBinds) $ \err ->
          pprPanic "Sequent Core Lint error (in occurrence analysis)"
            (withPprStyle defaultUserStyle $ err)
        (binds', count) <- runSimplM $ simplModule env occBinds
        when dumping $ putMsg  $ text "SUMMARY" <+> int n
                              $$ text "---------"
                              $$ pprSimplCount count
                              $$ text "AFTER" <+> int n
                              $$ text "-------"
                              $$ pprTopLevelBinds binds'
        runLint "post-simpl" binds' (text "--- Original Sequent Core: ---"
                                     $$ pprTopLevelBinds occBinds)
        if isZeroSimplCount count
          then do
            when tracing $ putMsg  $  text "Done after"
                                  <+> int n <+> text "iterations"
            return binds'
          else go (n+1) (count:prevCounts) binds'
    
    runOccurAnal env mod vects vectVars binds
      = let isRuleActive = activeRule env
        in occurAnalysePgm mod isRuleActive rules vects vectVars binds
    
    runLint hdr binds extraDoc
      = when linting $ whenIsJust (lintCoreBindings binds) $ \err ->
          pprPgmError ("Sequent Core Lint error (" ++ hdr ++ ")")
            (withPprStyle defaultUserStyle $ err
                                          $$ pprTopLevelBinds binds 
                                          $$ extraDoc)
      

simplModule :: SimplEnv -> [InBind] -> SimplM [OutBind]
simplModule env binds
  = do
    finalEnv <- simplBinds env binds TopLevel
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
simplCommand env (Eval term (Kont fs end))
  = simplTermInCommand env term (staticPart env) Nothing fs end
simplCommand env (Jump args j)
  = simplJump env args j

simplTermNoFloats :: SimplEnv -> InTerm -> SimplM OutTerm
simplTermNoFloats env (Compute ty comm)
  = do
    let (env', ty') = enterKontScope env ty
    comm' <- simplCommandNoFloats env' comm
    return $ mkCompute ty' comm'
simplTermNoFloats env term
  = do
    (env', term') <- simplTerm (zapFloats env) term
    return $ wrapFloatsAroundTerm env' term'

simplTerm :: SimplEnv -> InTerm -> SimplM (SimplEnv, OutTerm)
simplTerm env (Type ty)
  = return (env, Type (substTy env ty))
simplTerm env (Coercion co)
  = return (env, Coercion (simplCoercion env co))
simplTerm env (Compute ty comm)
  = do
    let (env', ty') = enterKontScope env ty
    -- Terms are closed with respect to continuation variables, so they can
    -- safely float past this binder. Continuations must *never* float past it,
    -- however, because they necessarily invoke the continuation bound here.
    (env'', comm') <- simplCommandNoKontFloats (zapFloats env') comm
    return (env `addFloats` env'', mkCompute ty' comm')
simplTerm env v
  = do
    let (env', ty') = enterKontScope env ty
        env'' = zapFloats env'
    (env''', comm) <- simplTermInCommand env'' v (staticPart env'') Nothing [] Return
    return (env, mkCompute ty' (wrapFloats env''' comm))
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
  , Type ty <- assert (isTypeArg v) v
  = let ty' = substTy (env_v `inDynamicScope` env_x) ty
    in return $ extendTvSubst env_x x ty'
  | isCoVar x
  , Coercion co <- assert (isCoArg v) v
  = let co' = simplCoercion (env_v `inDynamicScope` env_x) co
    in return $ extendCvSubst env_x x co'
  | otherwise
  = do
    preInline <- preInlineUnconditionally env_x env_v (BindTerm x v) level
    if preInline
      then do
        tick (PreInlineUnconditionally x)
        let rhs = Susp env_v v
            env' = extendIdSubst env_x x rhs
        return env'
      else do
        -- TODO Handle floating type lambdas
        let env_v' = zapFloats (env_v `inDynamicScope` env_x)
        (env_v'', v') <- simplTerm env_v' v
        (env_v_final, v'') <- prepareRhsTerm env_v'' level x' v'
        (env_x', v''')
          <- if not (doFloatFromRhs level recFlag False v'' env_v_final)
                then    return (env_x, wrapFloatsAroundTerm env_v_final v'')
                else do tick LetFloatFromLet
                        return (env_x `addFloats` env_v_final, v'')
        completeBind env_x' x x' (Left v''') level

-- c.f. Simplify.simplNonRecX
simplNonRecOut :: SimplEnv -> InId -> OutTerm -> SimplM SimplEnv
simplNonRecOut env bndr rhs
  | isDeadBinder bndr
  = return env
  | Coercion co <- rhs
  = return (extendCvSubst env bndr co)
  | otherwise
  = let (env', bndr') = enterScope env bndr
    in completeNonRecOut env' NotTopLevel (isStrictId bndr) bndr bndr' rhs

-- c.f. Simplify.completeNonRecX
completeNonRecOut :: SimplEnv -> TopLevelFlag -> Bool -> InId -> OutId
                  -> OutTerm -> SimplM SimplEnv
completeNonRecOut env level isStrict bndr bndr' rhs
  = do
    (env', rhs')   <- prepareRhsTerm (zapFloats env) level bndr' rhs
    (env'', rhs'') <-
      if doFloatFromRhs level NonRecursive isStrict rhs' env'
        then do
             tick LetFloatFromLet
             return (addFloats env env', rhs')
        else return (env, wrapFloatsAroundTerm env' rhs')
    completeBind env'' bndr bndr' (Left rhs'') level

prepareRhsTerm :: SimplEnv -> TopLevelFlag -> OutId -> OutTerm
               -> SimplM (SimplEnv, OutTerm)
prepareRhsTerm env _ _ v
  | isTrivialTerm v
  = return (env, v)
prepareRhsTerm env level x (Compute ty comm)
  = do
    (env', term') <- prepComm env comm
    return (env', term')
  where
    prepComm env (Eval term (Kont fs Return))
      = do
        (_isExp, env', fs', co_maybe) <- go (0 :: Int) fs
        case co_maybe of
          Just co -> do
                     let Pair fromTy toTy = coercionKind co
                     -- Don't use mkFreshKontId here because it sets the current continuation
                     (env'', x') <- mkFreshVar env' (fsLit "ca") fromTy
                     -- x' shares its strictness and demand info with x, since
                     -- x only adds a cast to x'
                     let info = idInfo x
                         sanitizedInfo = vanillaIdInfo `setStrictnessInfo` strictnessInfo info
                                                       `setDemandInfo` demandInfo info
                         x'_final = x' `setIdInfo` sanitizedInfo
                         x'_rhs = mkCompute fromTy (Eval term (Kont fs' Return))
                     if isTrivialTerm x'_rhs
                       then -- No sense turning one trivial term into two, as
                            -- the simplifier will just end up substituting one
                            -- into the other and keep on looping
                            return (env', Compute toTy (Eval term (Kont (fs' ++ [Cast co]) Return)))
                       else do
                            env''' <- completeNonRecOut env'' level False x'_final x'_final x'_rhs
                            x'_final_value <- simplVar env''' x'_final
                            return (env''', Compute toTy (Eval x'_final_value (Kont [Cast co] Return)))
          Nothing -> return (env', Compute ty (Eval term (Kont fs' Return)))
      where
        -- The possibility of a coercion split makes all of this tricky. Suppose
        -- we have
        --
        --   let x = compute (p :: Cont# b). < v | ... `cast` (g :: a ~ b); ret p >
        --
        -- where the ellipses indicate some arguments and inner coercions. We're
        -- going to want to split this in two:
        --   
        --   let x' = compute (q :: Cont# a). < v | ... ret q >
        --       x  = compute (p :: Cont# b). < x' | `cast` (g :: a ~ b); ret p >
        --
        -- Now we get to inline x everywhere and hope to find more redexes (see
        -- Note [Float coercions] in GHC Simplify.lhs).
        -- 
        -- Whether or not we do the split, the arguments in the ellipses will
        -- get ANF'd if we learn that this is an expandable application (a PAP
        -- or application of a constructor or CONLIKE function).
        --
        -- The protocol: go nValArgs kont takes the number of value args seen
        -- so far and the remaining continuation. It returns:
        --
        --   * True iff it turns out this is an expandable application
        --   * An updated environment, perhaps with some new bindings floated
        --   * A list of frames, represented as the ellipses above. If we do a
        --     coercion split, these will end up in the new binding; otherwise,
        --     they will stay in the original one.
        --   * The top-level coercion, if we're doing a coercion split.
        -- 
        -- TODO It would be easier to pass everything downward instead,
        -- employing a bit of knot-tying for the Bool, but for some reason
        -- there's no MonadFix CoreM, so we can't write MonadFix SimplM.
        go :: Int -> [OutFrame] -> SimplM (Bool, SimplEnv, [OutFrame], Maybe OutCoercion)
        go nValArgs (App (Type ty) : fs)
          = prepending (App (Type ty)) $ go nValArgs fs
        go nValArgs (App arg : fs)
          = do
            (isExp, env', fs', split) <- go (nValArgs+1) fs
            if isExp
              then do
                   (env'', arg') <- makeTrivial level env' arg
                   return (True,  env'', App arg' : fs', split)
              else return (False, env',  App arg  : fs', split)
        go nValArgs [Cast co]
          | let Pair fromTy _toTy = coercionKind co
          , not (isUnLiftedType fromTy) -- Don't coercion-split on unlifted type
          = return (isExpFor nValArgs, env, [], Just co)
        go nValArgs (Cast co : fs)
          = prepending (Cast co) $ go nValArgs fs
        go nValArgs []
          = return (isExpFor nValArgs, env, [], Nothing)
        go _ _
          = return (False, env, [], Nothing)
        
        isExpFor nValArgs
          | Var f <- term = isExpandableApp f nValArgs
          | otherwise     = False
        
        prepending f m
          = do { (isExp, env', fs, split) <- m; return (isExp, env', f : fs, split) }
    prepComm env comm
      = return (env, Compute ty comm)
prepareRhsTerm env _ _ term
  = return (env, term)

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
        let rhs = Susp env_pk pk
            env' = extendPvSubst env_j j rhs
        return env'
      else do
        (env_j', xs', comm') <-
          case pk of
            PKont [] comm -> do
              -- No parameters, so we can float things out
              let env_pk' = zapFloats (env_pk `inDynamicScope` env_j)
              (env_with_floats, comm') <- simplCommand env_pk' comm
              env_j'
                <- if isEmptyFloats env_with_floats
                      then return env_j
                      else do tick LetFloatFromLet -- Can always float through a cont binding
                              return $ env_j `addFloats` env_with_floats
              return (env_j', [], comm')
            PKont xs comm -> do
              -- There are parameters, so no floating
              let (env_pk', xs') = enterScopes (env_pk `inDynamicScope` env_j) xs
              comm' <- simplCommandNoFloats env_pk' comm
              return (env_j, xs', comm')
        completeBind env_j' j j' (Right (PKont xs' comm')) NotTopLevel

-- | Bind a continuation as the current one (as bound by a Compute). Unlike with
-- simplLazyBind and simplPKontBind, here we *have* to substitute since we can't
-- give a continuation a let binding.
simplKontBind :: SimplEnv -> Type -> StaticEnv -> InKont -> SimplM SimplEnv
simplKontBind env ty env_k k
  | tracing
  , pprTraceShort "simplKontBind" (text "ret" <+> dcolon <+> ppr ty $$ ppr k) False
  = undefined
  | otherwise
  = do
    -- For now, we use Susp as if the id were definitely used only once. If we
    -- go into a multi-branch case, we'll call mkDupableKont then.
    return $ env' `setRetKont` SynKont { mk_state = SuspKont env_k, mk_kont = k }
  where
    (env', _) = enterKontScope env ty

completeBind :: SimplEnv -> InVar -> OutVar -> OutRhs
             -> TopLevelFlag -> SimplM SimplEnv
completeBind env x x' v level
  = do
    (newArity, v') <- tryEtaExpandRhs env x' v
    postInline <- postInlineUnconditionally env (mkBindPair x v') level
    if postInline
      then do
        tick (PostInlineUnconditionally x)
        -- Nevermind about substituting x' for x; we'll substitute v' instead
        return $ either (extendIdSubst env x . Done) (extendPvSubst env x . Done) v'
      else do
        def <- mkDef env level v'
        let info' = idInfo x `setArityInfo` newArity
            (env', x'') = setDef env (x' `setIdInfo` info') def
        when tracing $ liftCoreM $ putMsg (text "defined" <+> ppr x'' <+> equals <+> ppr def)
        return $ addNonRecFloat env' (mkBindPair x'' v')

tryEtaExpandRhs :: SimplEnv -> OutId -> OutRhs -> SimplM (Arity, OutRhs)
tryEtaExpandRhs env x (Left v)
  = do (arity, v') <- tryEtaExpandRhsTerm env x v
       return (arity, Left v')
tryEtaExpandRhs _ _ (Right pk@(PKont xs _))
  = return (length (filter isId xs), Right pk)

tryEtaExpandRhsTerm :: SimplEnv -> OutId -> OutTerm -> SimplM (Arity, OutTerm)
-- See Note [Eta-expanding at let bindings]
-- and Note [Eta expansion to manifest arity]
tryEtaExpandRhsTerm env bndr rhs
  = do { dflags <- getDynFlags
       ; (new_arity, new_rhs) <- try_expand dflags

       ; warnPprTrace (new_arity < old_arity) __FILE__ __LINE__ (
               (ptext (sLit "Arity decrease:") <+> (ppr bndr <+> ppr old_arity
                <+> ppr new_arity) $$ ppr new_rhs) )
                        -- Note [Arity decrease]
         return (new_arity, new_rhs) }
  where
    try_expand dflags
      | isTrivialTerm rhs
      = return (termArity rhs, rhs)

      | sm_eta_expand (getMode env)      -- Provided eta-expansion is on
      , let new_arity = findRhsArity dflags bndr rhs old_arity
      , new_arity > manifest_arity      -- And the curent manifest arity isn't enough
      = do { tick (EtaExpansion bndr)
           ; return (new_arity, etaExpand new_arity rhs) }
      | otherwise
      = return (manifest_arity, rhs)

    manifest_arity = manifestArity rhs
    old_arity  = idArity bndr

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

simplTermInCommand :: SimplEnv -> InTerm
                   -> StaticEnv -> Maybe InCoercion -> [InFrame] -> InEnd
                   -> SimplM (SimplEnv, OutCommand)
simplTermInCommand env_v v env_k co_m fs end
  | tracing
  , pprTraceShort "simplTermInCommand" (
      ppr env_v $$ ppr v $$ maybe empty showCo co_m $$ ppr env_k $$ ppr (Kont fs end)
    ) False
  = undefined
  where
    showCo co = text "coercing:" <+> ppr fromTy <+> darrow <+> ppr toTy
      where Pair fromTy toTy = coercionKind co
simplTermInCommand _ (Type ty) _ _ _ _
  = pprPanic "simplTermInCommand" (ppr ty)
simplTermInCommand env_v (Var x) env_k co_m fs end
  = case substId env_v x of
      DoneId x'
        -> do
           let lone | App {} : _ <- fs = False
                    | otherwise        = True
           let term'_maybe = callSiteInline env_v x' (activeUnfolding env_v x')
                                            lone (Kont fs end)
           case term'_maybe of
             Nothing
               -> simplTermInCommandDone env_v (Var x') env_k co_m fs end
             Just term'
               -> do
                  tick (UnfoldingDone x')
                  simplTermInCommand (zapSubstEnvs env_v) term' env_k co_m fs end
      Done v
        -- Term already simplified (then PostInlineUnconditionally'd), so
        -- don't do any substitutions when processing it again
        -> simplTermInCommand (zapSubstEnvs env_v) v env_k co_m fs end
      Susp stat v
        -> simplTermInCommand (env_v `setStaticPart` stat) v env_k co_m fs end
simplTermInCommand env_v (Compute ty c) env_k co_m fs end
  = do
    env_v' <- simplKontBind env_v ty env_k (Kont (co_m `consCastMaybe` fs) end)
    simplCommand env_v' c
simplTermInCommand env_v v env_k co_m (Cast co' : fs) end
  = simplTermInCommand env_v v env_k (combineCo co_m co') fs end
simplTermInCommand env_v v@(Coercion co) env_k co_m fs end
  = simplTermInCommandDone env_v v' env_k Nothing fs end
  where
    v' = case co_m of
           Just co' -> Coercion (mkCoCast co co')
           Nothing  -> v
-- discard a non-counting tick on a lambda.  This may change the
-- cost attribution slightly (moving the allocation of the
-- lambda elsewhere), but we don't care: optimisation changes
-- cost attribution all the time. (comment from Simplify.simplLam)
simplTermInCommand env_v v@(Lam {}) env_k co_m (Tick ti : fs) end
  | not (tickishCounts ti)
  = simplTermInCommand env_v v env_k co_m fs end
simplTermInCommand env_v (Lam x body) env_k co_m (App arg : fs) end
  = do
    tick (BetaReduction x)
    let (arg', co_m') = castApp arg co_m
    env_v' <- simplNonRec env_v x env_k arg' NotTopLevel
    simplTermInCommand env_v' body env_k co_m' fs end
simplTermInCommand env_v term@(Lam {}) env_k co_m fs end
  = do
    let (xs, body) = lambdas term
        (env_v', xs') = enterScopes env_v xs
    body' <- simplTermNoFloats env_v' body
    simplTermInCommandDone env_v (mkLambdas xs' body') env_k co_m fs end
simplTermInCommand env_v term@(Lit {}) env_k co_m fs end
  = simplTermInCommandDone env_v term env_k co_m fs end

simplTermInCommandDone :: SimplEnv -> OutTerm
                       -> StaticEnv -> Maybe InCoercion -> [InFrame] -> InEnd
                       -> SimplM (SimplEnv, OutCommand)
simplTermInCommandDone env_v v env_k co_m fs end
  = simplKont env (mkArgInfo env v co_m fs) fs end
  where
    env = env_k `inDynamicScope` env_v

simplKont :: SimplEnv -> ArgInfo -> [InFrame] -> InEnd -> SimplM (SimplEnv, OutCommand)
simplKont env ai fs end
  | tracing
  , pprTraceShort "simplKont" (
      ppr env $$ ppr ai $$ ppr (Kont fs end)
    ) False
  = undefined
simplKont env ai (Cast co : fs) end
  = simplKont env (ai { ai_co = ai_co ai `combineCo` co }) fs end
simplKont env ai fs@(App _ : _) end
  | Just co <- ai_co ai
  , let Pair fromTy _toTy = coercionKind co
  , Nothing <- splitFunTy_maybe fromTy
  , Nothing <- splitForAllTy_maybe fromTy
  -- Can't push the cast after the arguments, so eat it
  = simplKont env (swallowCoercion env ai) fs end
simplKont env ai (App arg@(Type tyArg) : fs) end
  = do
    let (_, co_m') = castApp arg (ai_co ai) -- castApp doesn't change type args
        ty' = substTy env tyArg
    simplKont env (ai { ai_frames = App (Type ty') : ai_frames ai
                      , ai_co = co_m' }) fs end
simplKont env (ai@ArgInfo { ai_strs = [] }) fs end
  -- We've run out of strictness arguments, meaning the call is definitely bottom
  | not (null fs && isReturn end) -- Don't bother throwing away a trivial continuation
  = simplKontDone env ai (Case (mkWildValBinder ty) [])
  where
    ty = termType (argInfoToTerm env ai)
simplKont _ (ArgInfo { ai_discs = [] }) _ _
  = pprPanic "simplKont" (text "out of discounts??")
simplKont env ai@(ArgInfo { ai_strs = str:strs
                          , ai_discs = disc:discs }) (App arg : fs) end
  | str
  = do
    -- Push the current evaluation state into the environment as a
    -- meta-continuation. We'll continue with the rest of the frames when we
    -- finish simplifying the term. This, of course, reflects left-to-right
    -- call-by-value evaluation.
    let mk = StrictArg { mk_state = SuspKont (staticPart env)
                       , mk_argInfo = ai'
                       , mk_frames = fs
                       , mk_end = end }
        (env', _ty') = enterKontScope env (termType arg)
        env_final    = env' `setRetKont` mk
    simplCommand env_final (Eval arg' (Kont [] Return))
  | otherwise
  = do
    -- Don't float out of lazy arguments (see Simplify.rebuildCall)
    arg_final <- simplTermNoFloats env arg'
    simplKont env (ai' { ai_frames = App arg_final : ai_frames ai' }) fs end
  where
    (arg', co_m') = castApp arg (ai_co ai)
    ai' = ai { ai_strs = strs, ai_discs = discs, ai_co = co_m' }
simplKont env ai (f@(Tick _) : fs) end
  -- FIXME Tick handling is actually rather delicate! In fact, we should
  -- (somehow) be putting a float barrier here (see Simplify.simplTick).
  = simplKont env (addFrameToArgInfo env ai f) fs end
simplKont env ai@(ArgInfo { ai_co = Just _ }) [] end
  = simplKont env (swallowCoercion env ai) [] end
-- From now on, no coercion
simplKont env ai@(ArgInfo { ai_term = Var fun, ai_rules = rules }) [] end
  | not (null rules || skip_rules)
  = do
    let (args, fs') = argInfoSpanArgs ai
    match_maybe <- tryRules env rules fun args
    case match_maybe of
      Just (ruleRhs, extraArgs) ->
        -- spliceFrames will save the current environment in the metacontinuation,
        -- so we're free to zap the subst envs
        let env' = zapTermSubstEnvs (spliceFrames env (map App extraArgs ++ fs') end)
        in simplTermInCommand env' ruleRhs (staticPart env') Nothing [] Return
      Nothing -> simplKontAfterRules env ai end
  where
    -- If the metacontinuation just wants to give us more arguments, let rules
    -- wait until we have them
    skip_rules = case substKv env of
                   Just (SynKont {})         -> True
                   Just (AppendOutFrames {}) -> True
                   _                         -> False
simplKont env ai [] end
  = simplKontAfterRules env ai end

simplKontAfterRules :: SimplEnv -> ArgInfo -> InEnd
                    -> SimplM (SimplEnv, OutCommand)
simplKontAfterRules _ (ArgInfo { ai_co = Just co }) _
  = pprPanic "simplKontAfterRules" (text "Leftover coercion:" <+> ppr co)
simplKontAfterRules env ai (Case x alts)
  | Lit lit <- ai_term ai
  , not (litIsLifted lit)
  , null (ai_frames ai) -- TODO There could be ticks here; deal with them
  = do
    tick (KnownBranch x)
    case matchCase env (LitVal lit) alts of
      Nothing -> missingAlt env x alts
      Just (Alt _ binds rhs) -> bindCaseBndr binds rhs
  | Just (dc, tyArgs, valArgs) <- termIsConApp_maybe env (getUnfoldingInRuleMatch env) scrut
  = do
    tick (KnownBranch x)
    case matchCase env (ConsVal dc tyArgs valArgs) alts of
      Nothing -> missingAlt env x alts
      Just (Alt DEFAULT binds rhs) -> bindCaseBndr binds rhs
      Just (Alt _       binds rhs) -> knownCon env scrut dc tyArgs valArgs x binds rhs 
  where
    scrut = argInfoToTerm env ai
    bindCaseBndr binds rhs
      = assert (null binds) $ do
        env' <- simplNonRecOut env x scrut
        simplCommand env' rhs
simplKontAfterRules env ai (Case case_bndr [Alt _ bndrs rhs])
 | all isDeadBinder bndrs       -- bndrs are [InId]
 
 , if isUnLiftedType (idType case_bndr)
   then elim_unlifted        -- Satisfy the let-binding invariant
   else elim_lifted
  = do  { -- pprTraceShort "case elim" (vcat [ppr case_bndr, ppr (exprIsHNF scrut),
          --                            ppr ok_for_spec,
          --                            ppr scrut]) $
          tick (CaseElim case_bndr)
        ; env' <- simplNonRecOut env case_bndr scrut
        ; simplCommand env' rhs }
  where
    elim_lifted   -- See Note [Case elimination: lifted case]
      = termIsHNF env scrut
     || (is_plain_seq && ok_for_spec)
              -- Note: not the same as exprIsHNF
     || case_bndr_evald_next rhs
 
    elim_unlifted
      | is_plain_seq = termOkForSideEffects scrut
            -- The entire case is dead, so we can drop it,
            -- _unless_ the scrutinee has side effects
      | otherwise    = ok_for_spec
            -- The case-binder is alive, but we may be able
            -- turn the case into a let, if the expression is ok-for-spec
            -- See Note [Case elimination: unlifted case]
 
    ok_for_spec      = termOkForSpeculation scrut
    is_plain_seq     = isDeadBinder case_bndr -- Evaluation *only* for effect
 
    case_bndr_evald_next :: SeqCoreCommand -> Bool
      -- See Note [Case binder next]
    case_bndr_evald_next (Eval (Var v) _) = v == case_bndr
    case_bndr_evald_next _                = False
      -- Could allow for let bindings,
      -- but the original code in Simplify suggests doing so would be expensive
      
    scrut = argInfoToTerm env ai
simplKontAfterRules env ai (Case x alts)
  = do
    env' <- if length alts > 1
              then ensureDupableKont env -- we're about to duplicate the context
              else return env
    let (env_alts, x') = enterScope env' x
        ai' = swallowCoercion env ai
        scrut = argInfoToTerm env ai'
    
    alts' <- forM alts (simplAlt env_alts (Just scrut) [] x')
    simplKontDone env' ai' (Case x' alts')
simplKontAfterRules env ai Return
  = case substKv env of
      Nothing
        -> simplKontDone env ai Return
      Just mk@(SynKont { mk_kont = Kont fs end })
        -> simplKont (envFrom mk) ai fs end
      Just mk@(StrictArg { mk_argInfo = ai'
                         , mk_frames = fs
                         , mk_end = end })
        -> let arg  = argInfoToTerm env ai
               env' = envFrom mk
           in simplKont env' (addFrameToArgInfo env' ai' (App arg)) fs end
      Just mk@(AppendOutFrames { mk_outFrames = fs })
        -> let env' = envFrom mk
           in simplKont env' (addFramesToArgInfo env ai fs) [] Return
             -- Pass old environment because that's the environment of ai's coercion
  where
    envFrom mk = env `setStaticPartFrom` mk

simplKontDone :: SimplEnv -> ArgInfo -> OutEnd -> SimplM (SimplEnv, OutCommand)
simplKontDone env ai end
  | tracing
  , pprTrace "simplKontDone" (ppr env $$ ppr ai $$ ppr end) False
  = undefined
  | otherwise
  = return (env, Eval term (Kont (reverse fs) end))
  where ArgInfo { ai_term = term, ai_frames = fs } = swallowCoercion env ai

simplAlt :: SimplEnv -> Maybe OutTerm -> [AltCon] -> OutId -> InAlt -> SimplM OutAlt
simplAlt env _scrut_maybe _notAmong _caseBndr (Alt con xs c)
  = do
    -- TODO Important: Update definitions! This is likely to be low-hanging
    -- fruit. This is why we take the scrutinee, other constructors, and case
    -- binder as arguments.
    let (env', xs') = enterScopes env xs
    c' <- simplCommandNoFloats env' c
    return $ Alt con xs' c'

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

knownCon :: SimplEnv
         -> OutTerm                             -- The scrutinee
         -> DataCon -> [OutType] -> [OutTerm]   -- The scrutinee (in pieces)
         -> InId -> [InBndr] -> InCommand       -- The alternative
         -> SimplM (SimplEnv, OutCommand)
knownCon env scrut dc tyArgs valArgs bndr binds rhs
  = do
    env'  <- bindArgs env binds valArgs
    env'' <- bindCaseBndr env'
    simplCommand env'' rhs
  where
    -- If b isn't dead, make sure no bound variables are marked dead
    zap_occ b | isDeadBinder bndr = b
              | otherwise         = zapIdOccInfo b
    
    bindArgs env' []      _                = return env'
    bindArgs env' (b:bs') (Type ty : args) = assert (isTyVar b) $
                                             bindArgs (extendTvSubst env' b ty) bs' args
    bindArgs env' (b:bs') (arg : args)     = assert (isId b) $ do
                                             let b' = zap_occ b
                                             env'' <- simplNonRecOut env' b' arg
                                             bindArgs env'' bs' args
    bindArgs _    _       _                = pprPanic "bindArgs" $ ppr dc $$ ppr binds $$ ppr valArgs $$
                                               text "scrut:" <+> ppr scrut
    
       -- It's useful to bind bndr to scrut, rather than to a fresh
       -- binding      x = Con arg1 .. argn
       -- because very often the scrut is a variable, so we avoid
       -- creating, and then subsequently eliminating, a let-binding
       -- BUT, if scrut is a not a variable, we must be careful
       -- about duplicating the arg redexes; in that case, make
       -- a new con-app from the args (comment from Simplify.knownCon)
    bindCaseBndr env
      | isDeadBinder bndr   = return env
      | isTrivialTerm scrut = return (extendIdSubst env bndr (Done scrut))
      | otherwise           = do { args <- mapM (simplVar env) binds
                                         -- tyArgs are aready OutTypes,
                                         -- but binds are InBndrs
                                 ; let con_app = mkCompute (substTy env (idType bndr)) $
                                                 Eval (Var (dataConWorkId dc))
                                                      (Kont (map (App . Type) tyArgs ++
                                                             map App args) Return)
                                 ; simplNonRecOut env bndr con_app }

missingAlt :: SimplEnv -> Id -> [InAlt] -> SimplM (SimplEnv, OutCommand)
                -- This isn't strictly an error, although it is unusual.
                -- It's possible that the simplifer might "see" that
                -- an inner case has no accessible alternatives before
                -- it "sees" that the entire branch of an outer case is
                -- inaccessible.  So we simply put an error case here instead.
                -- (comment from Simplify.missingAlt)
missingAlt env case_bndr _
  = warnPprTrace True __FILE__ __LINE__ ( ptext (sLit "missingAlt") <+> ppr case_bndr )
    return (env, mkImpossibleCommand (retType env))

-- When we simplify a rule's RHS, we need to do it in an environment where
-- the bound continuation:
--
--   1. applies leftover arguments,
--   2. performs the end of the original continuation, and then
--   3. delegates to the original environment's continuation.
--
-- We can't combine 1 and 2 because we want to skip the leftover arguments
-- without re-simplifying them but we don't want to skip the end.
--
-- Each of parts 1 and 2, if nontrivial, requires that we set up a new
-- environment with whose metacontinuation delegates to the environment in
-- the next part.
spliceFrames :: SimplEnv -> [OutFrame] -> InEnd -> SimplEnv
spliceFrames env frames end
  | null frames = envWithEnd -- part 1 is trivial
  | otherwise   = env `setRetKont` AppendOutFrames { mk_state = SuspKont (staticPart envWithEnd)
                                                   , mk_outFrames = frames }
  where
    envWithEnd | Return <- end = env -- part 2 is trivial
               | otherwise     = env `setRetKont` SynKont { mk_state = SuspKont (staticPart env)
                                                          , mk_kont  = Kont [] end }

-------------------
-- Rewrite rules --
-------------------

tryRules :: SimplEnv -> [CoreRule]
         -> Id -> [OutArg]
         -> SimplM (Maybe (OutTerm, [OutArg]))
tryRules env rules fn args
  | null rules
  = return Nothing
  | otherwise
  = do { dflags <- getDynFlags
       ; case lookupRule dflags (getInScopeSet env, getUnfoldingInRuleMatch env)
                         (activeRule env) fn coreArgs rules of {
           Nothing               -> return Nothing ;   -- No rule matches
           Just (rule, rule_rhs) ->
             do { checkedTick (RuleFired (ru_name rule))
                ; dump dflags rule rule_rhs
                ; let term' = termFromCoreExpr rule_rhs
                ; let extraArgs = drop (ruleArity rule) args
                      -- (ruleArity rule) says how many args the rule consumed
                      
                ; return (Just (term', extraArgs)) }}}
  where
    coreArgs = map termToCoreExpr args
        
    dump dflags rule rule_rhs
      | dopt Opt_D_dump_rule_rewrites dflags
      = log_rule dflags Opt_D_dump_rule_rewrites "Rule fired" $ vcat
          [ text "Rule:" <+> ftext (ru_name rule)
          , text "Before:" <+> hang (ppr fn) 2 (sep (map ppr $ take arity args))
          , text "After: " <+> ppr rule_rhs
          , text "Cont:  " <+> ppr (Kont (map App $ drop arity args) Return) ]

      | dopt Opt_D_dump_rule_firings dflags
      = log_rule dflags Opt_D_dump_rule_firings "Rule fired:" $
          ftext (ru_name rule)

      | otherwise
      = return ()
      where
        arity = ruleArity rule

    log_rule dflags flag hdr details = liftIO . dumpSDoc dflags flag "" $
      sep [text hdr, nest 4 details]

--------------
-- Inlining --
--------------

-- Based on preInlineUnconditionally in SimplUtils; see comments there
preInlineUnconditionally :: SimplEnv -> StaticEnv -> InBindPair
                         -> TopLevelFlag -> SimplM Bool
preInlineUnconditionally env_x _env_rhs pair level
  = do
    ans <- go (getMode env_x) <$> getDynFlags
    when tracing $ liftCoreM $ putMsg $ text "preInline" <+> ppr x <> colon <+> text (show ans)
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
        canInlineInLam c
          | Just v <- asValueCommand c   = canInlineTermInLam v
          | otherwise                    = False
        canInlineTermInLam (Lit _)       = True
        canInlineTermInLam (Lam x t)     = isRuntimeVar x
                                         || canInlineTermInLam t
        canInlineTermInLam (Compute _ c) = canInlineInLam c
        canInlineTermInLam _             = False
        early_phase = case sm_phase mode of
                        Phase 0 -> False
                        _       -> True

-- Based on postInlineUnconditionally in SimplUtils; see comments there
postInlineUnconditionally :: SimplEnv -> OutBindPair -> TopLevelFlag
                          -> SimplM Bool
postInlineUnconditionally env pair level
  = do
    ans <- go (getMode env) <$> getDynFlags
    when tracing $ liftCoreM $ putMsg $ text "postInline" <+> ppr (binderOfPair pair) <> colon <+> text (show ans)
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

computeDiscount :: DynFlags -> Arity -> [Int] -> Int -> [ArgSummary] -> CallCtxt
                -> Int
computeDiscount dflags uf_arity arg_discounts res_discount arg_infos cont_info
         -- We multiple the raw discounts (args_discount and result_discount)
        -- ty opt_UnfoldingKeenessFactor because the former have to do with
        --  *size* whereas the discounts imply that there's some extra 
        --  *efficiency* to be gained (e.g. beta reductions, case reductions) 
        -- by inlining.

  = 10          -- Discount of 1 because the result replaces the call
                -- so we count 1 for the function itself

    + 10 * length (take uf_arity arg_infos)
                  -- Discount of (un-scaled) 1 for each arg supplied, 
                  -- because the result replaces the call

    + round (ufKeenessFactor dflags *
             fromIntegral (arg_discount + res_discount'))
  where
    arg_discount = sum (zipWith mk_arg_discount arg_discounts arg_infos)

    mk_arg_discount _              TrivArg    = 0 
    mk_arg_discount _        NonTrivArg = 10
    mk_arg_discount discount ValueArg   = discount 

    res_discount' = case cont_info of
                        BoringCtxt  -> 0
                        CaseCtxt    -> res_discount  -- Presumably a constructor
                        ValAppCtxt  -> res_discount  -- Presumably a function
                        _           -> 40 `min` res_discount
                -- ToDo: this 40 `min` res_dicount doesn't seem right
                --   for DiscArgCtxt it shouldn't matter because the function will
                --    get the arg discount for any non-triv arg
                --   for RuleArgCtxt we do want to be keener to inline; but not only
                --    constructor results
                --   for RhsCtxt I suppose that exposing a data con is good in general
                --   And 40 seems very arbitrary
                --
                -- res_discount can be very large when a function returns
                -- constructors; but we only want to invoke that large discount
                -- when there's a case continuation.
                -- Otherwise we, rather arbitrarily, threshold it.  Yuk.
                -- But we want to aovid inlining large functions that return 
                -- constructors into contexts that are simply "interesting"

data CallCtxt
  = BoringCtxt
  | RhsCtxt             -- Rhs of a let-binding; see Note [RHS of lets]
  | DiscArgCtxt         -- Argument of a fuction with non-zero arg discount
  | RuleArgCtxt         -- We are somewhere in the argument of a function with rules

  | ValAppCtxt          -- We're applied to at least one value arg
                        -- This arises when we have ((f x |> co) y)
                        -- Then the (f x) has argument 'x' but in a ValAppCtxt

  | CaseCtxt            -- We're the scrutinee of a case
                        -- that decomposes its scrutinee

instance Outputable CallCtxt where
  ppr CaseCtxt    = ptext (sLit "CaseCtxt")
  ppr ValAppCtxt  = ptext (sLit "ValAppCtxt")
  ppr BoringCtxt  = ptext (sLit "BoringCtxt")
  ppr RhsCtxt     = ptext (sLit "RhsCtxt")
  ppr DiscArgCtxt = ptext (sLit "DiscArgCtxt")
  ppr RuleArgCtxt = ptext (sLit "RuleArgCtxt")

callSiteInline :: SimplEnv -> OutId -> Bool -> Bool -> InKont -> Maybe OutTerm
callSiteInline env id active_unfolding lone_variable kont
  = case findDef env id of 
      -- idUnfolding checks for loop-breakers, returning NoUnfolding
      -- Things with an INLINE pragma may have an unfolding *and* 
      -- be a loop breaker  (maybe the knot is not yet untied)
      Just BoundTo { def_term = unf_template, def_level = is_top 
                   , def_isWorkFree = is_wf,  def_arity = uf_arity
                   , def_guidance = guidance, def_isExpandable = is_exp }
                   | active_unfolding -> let (arg_infos, cont_info) = distillKont kont
                                         in tryUnfolding (dynFlags env) id lone_variable
                                             arg_infos cont_info unf_template (isTopLevel is_top)
                                             is_wf is_exp uf_arity guidance
                   | tracing
                   -> pprTrace "Inactive unfolding:" (ppr id) Nothing
                   | otherwise -> Nothing
      _            -> Nothing

-- Impedence mismatch between Sequent Core code and logic from CoreUnfold.
-- TODO This never generates most of the CallCtxt values. Need to keep track of
-- more in able to answer more completely.
distillKont :: InKont -> ([ArgSummary], CallCtxt)
distillKont (Kont fs end) = (mapMaybe doFrame fs, doEnd end)
  where
    doFrame (App v)    = Just (interestingArg v)
    doFrame _          = Nothing
    
    doEnd (Return {})  = BoringCtxt
    doEnd (Case {})    = CaseCtxt

tryUnfolding :: DynFlags -> Id -> Bool -> [ArgSummary] -> CallCtxt
             -> OutTerm -> Bool -> Bool -> Bool -> Arity -> Guidance
             -> Maybe OutTerm
tryUnfolding dflags id lone_variable 
             arg_infos cont_info unf_template is_top 
             is_wf is_exp uf_arity guidance
                        -- uf_arity will typically be equal to (idArity id), 
                        -- but may be less for InlineRules
 | tracing
 = pprTrace ("Considering inlining: " ++ showSDocDump dflags (ppr id))
                 (vcat [text "arg infos" <+> ppr arg_infos,
                        text "uf arity" <+> ppr uf_arity,
                        text "interesting continuation" <+> ppr cont_info,
                        text "some_benefit" <+> ppr some_benefit,
                        text "is exp:" <+> ppr is_exp,
                        text "is work-free:" <+> ppr is_wf,
                        text "guidance" <+> ppr guidance,
                        extra_doc,
                        text "ANSWER =" <+> if yes_or_no then text "YES" else text "NO"])
                 result
  | otherwise  = result

  where
    n_val_args = length arg_infos
    saturated  = n_val_args >= uf_arity
    cont_info' | n_val_args > uf_arity = ValAppCtxt
               | otherwise             = cont_info

    result | yes_or_no = Just unf_template
           | otherwise = Nothing

    interesting_args = any nonTriv arg_infos 
            -- NB: (any nonTriv arg_infos) looks at the
            -- over-saturated args too which is "wrong"; 
            -- but if over-saturated we inline anyway.

           -- some_benefit is used when the RHS is small enough
           -- and the call has enough (or too many) value
           -- arguments (ie n_val_args >= arity). But there must
           -- be *something* interesting about some argument, or the
           -- result context, to make it worth inlining
    some_benefit 
       | not saturated = interesting_args        -- Under-saturated
                                                 -- Note [Unsaturated applications]
       | otherwise = interesting_args            -- Saturated or over-saturated
                  || interesting_call

    interesting_call 
      = case cont_info' of
          CaseCtxt   -> not (lone_variable && is_wf)  -- Note [Lone variables]
          ValAppCtxt -> True                          -- Note [Cast then apply]
          RuleArgCtxt -> uf_arity > 0  -- See Note [Unfold info lazy contexts]
          DiscArgCtxt -> uf_arity > 0  --
          RhsCtxt     -> uf_arity > 0  --
          _           -> not is_top && uf_arity > 0   -- Note [Nested functions]
                                                      -- Note [Inlining in ArgCtxt]

    (yes_or_no, extra_doc)
      = case guidance of
          Never -> (False, empty)

          Usually { guEvenIfUnsat = unsat_ok, guEvenIfBoring = boring_ok }
             -> (enough_args && (boring_ok || some_benefit), empty )
             where      -- See Note [INLINE for small functions (3)]
               enough_args = saturated || (unsat_ok && n_val_args > 0)

          Sometimes { guArgDiscounts = arg_discounts, guResultDiscount = res_discount,
                      guSize = size }
             -> ( is_wf && some_benefit && small_enough
                , (text "discounted size =" <+> int discounted_size) )
                 where
                   discounted_size = size - discount
                   small_enough = discounted_size <= ufUseThreshold dflags
                   discount = computeDiscount dflags uf_arity arg_discounts 
                                              res_discount arg_infos cont_info'

-------------------------------
-- Continuations and sharing --
-------------------------------

ensureDupableKont :: SimplEnv -> SimplM SimplEnv
ensureDupableKont env
  | Just kont <- substKv env
  , SuspKont stat <- mk_state kont
  = do
    (env', kont') <- mkDupableKont (stat `inDynamicScope` zapFloats env) ty kont
    return $ (env `addFloats` env') `setRetKont` kont'
  | otherwise
  = return env
  where
    ty = retType env

-- | Make a continuation into something we're okay with duplicating into each
-- branch of a case (and each branch of those branches, ...), possibly
-- generating a number of bound terms and join points in the process.
--
-- The rules:
--   1. Duplicate returns.
--   2. Duplicate casts.
--   3. Don't duplicate ticks (because GHC doesn't).
--   4. Duplicate applications, but ANF-ize them first to share the arguments.
--   5. Don't duplicate single-branch cases.
--   6. Duplicate cases, but "ANF-ize" in a dual sense by creating a join point
--        for each branch.

mkDupableKont :: SimplEnv -> Type -> MetaKont -> SimplM (SimplEnv, MetaKont)
mkDupableKont env _ty kont
  | canDupMetaKont kont
  = return (env, kont)
mkDupableKont env ty kont
  = do
    let env_noFloats = zapFloats env
    when tracing $ liftCoreM $ putMsg $
      hang (text "mkDupableKont") 4 (ppr env_noFloats $$ ppr ty $$ ppr kont)
    (env', ans) <- case kont of
      SynKont { mk_kont = Kont fs end }
        -> do
           (env', kont', mk_m) <- go env_noFloats [] ty fs end
           return (env', SynKont { mk_state = DupableKont mk_m, mk_kont = kont' })
      StrictArg { mk_argInfo = ai
                , mk_frames  = fs
                , mk_end     = end }
        -> do
           (env', Kont fs' end', mk_m) <- go env_noFloats [] ty fs end
           (env'', outFrames) <- mapAccumLM (makeTrivialFrame NotTopLevel) env' (ai_frames ai)
           return (env'', kont { mk_state   = DupableKont mk_m
                               , mk_argInfo = ai { ai_frames = outFrames }
                               , mk_frames  = fs'
                               , mk_end     = end' })
      AppendOutFrames { mk_outFrames = outFrames }
        -> do
           env' <- ensureDupableKont env_noFloats
                     -- Process the metacontinuation
           (env'', outFrames') <- mapAccumLM (makeTrivialFrame NotTopLevel) env' outFrames
           return (env'', AppendOutFrames { mk_state     = DupableKont (substKv env')
                                          , mk_outFrames = outFrames' })
           
    when tracing $ liftCoreM $ putMsg $ hang (text "mkDupableKont DONE") 4 $
      ppr ans $$ vcat (map ppr (getFloatBinds (getFloats env')))
    return (env `addFloats` env', ans)
  where
    go :: SimplEnv -> [OutFrame] -> OutType -> [InFrame] -> InEnd
       -> SimplM (SimplEnv, OutKont, Maybe MetaKont)
    go env fs' ty [] Return
      = case substKv env of
          Nothing                -> done env fs' Return Nothing
          Just mk                 | canDupMetaKont mk
                                 -> done env fs' Return (Just mk)
          Just (mk@SynKont {})   -> do
                                    let env' = env `setStaticPartFrom` mk
                                        Kont fs end = mk_kont mk
                                    go env' fs' ty fs end
          Just (mk@StrictArg {}) -> do
                                    let env' = env `setStaticPartFrom` mk
                                    (env'', mk') <- mkDupableKont env' ty mk
                                    done env'' fs' Return (Just mk')
          Just (mk@AppendOutFrames { mk_outFrames = frames }) -> do
                                    let env' = env `setStaticPartFrom` mk
                                    (env'', frames') <- mapAccumLM (makeTrivialFrame NotTopLevel) env' frames
                                    go env'' fs' (applyTypeToFrames ty frames') [] Return
    
    go env fs' _ty (Cast co : fs) end
      = let co' = simplCoercion env co
        in go env (Cast co' : fs') (pSnd (coercionKind co')) fs end
    
    go env fs' ty fs@(Tick {} : _) end
      = split env fs' ty fs end (fsLit "*tickj")
    
    go env fs' ty (App (Type tyArg) : fs) end
      = let tyArg' = substTy env tyArg
            ty'    = applyTy ty  tyArg'
        in go env (App (Type tyArg') : fs') ty' fs end
    
    go env fs' ty (App arg : fs) end
      = do
        (env', arg') <- mkDupableTerm env arg
        go env' (App arg' : fs') (funResultTy ty) fs end

    -- Don't duplicate seq (see Note [Single-alternative cases] in GHC Simplify.lhs)
    go env fs' ty [] end@(Case caseBndr [Alt _altCon bndrs _rhs])
      | all isDeadBinder bndrs
      , not (isUnLiftedType (idType caseBndr))
      = split env fs' ty [] end (fsLit "*seqj")

    go env fs' _ty [] (Case caseBndr alts)
      -- This is dual to the App case: We have several branches and we want to
      -- bind each to a join point.
      = do
        -- NOTE: At this point, mkDupableCont in GHC Simplify.lhs calls
        -- prepareCaseCont (ultimately a recursive call) on the outer
        -- continuation. We have no outer continuation for a case; in the
        -- equivalent situation, we would have already dealt with the outer
        -- case. May be worth checking that we get the same result.
        
        let (altEnv, caseBndr') = enterScope env caseBndr
        alts' <- mapM (simplAlt altEnv Nothing [] caseBndr') alts
        (env', alts'') <- mkDupableAlts env caseBndr' alts'
        
        done env' fs' (Case caseBndr' alts'') Nothing
        
    split :: SimplEnv -> [OutFrame] -> Type -> [InFrame] -> InEnd -> FastString
          -> SimplM (SimplEnv, OutKont, Maybe MetaKont)
    split env fs' ty fs end name
        -- XXX This is a bit ugly, but it is currently the only way to split a
        -- non-parameterized continuation in two:
        --   Edup[Knodup] ==> let cont j x = < x | Knodup >
        --                    in Edup[case of x -> < jump x | j >]
        -- Notice that it's only okay to put the case there because Knodup is a
        -- strict context, which is only necessarily true because all
        -- continuations are strict contexts. If that changes, we'll need to
        -- revisit this.
      = do
        let kontTy = mkKontTy (mkTupleTy UnboxedTuple [ty])
        (env', j) <- mkFreshVar env name kontTy
        let (env'', x) = enterScope env' (mkKontArgId ty)
            join_rhs  = PKont [x] (Eval (Var x) (Kont fs end))
            join_kont = Case x [Alt DEFAULT [] (Jump [Var x] j)]
        env_final <- simplPKontBind env'' j j (staticPart env'') join_rhs NonRecursive
        
        done env_final fs' join_kont Nothing
    
    done :: SimplEnv -> [OutFrame] -> OutEnd -> Maybe MetaKont
         -> SimplM (SimplEnv, OutKont, Maybe MetaKont)
    done env fs end mk_m = return (env, Kont (reverse fs) end, mk_m)
    
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
            argTy   = foldr mkUbxExistsTy (mkTupleTy UnboxedTuple bndrTys) tyBndrs
        
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
    
    go n (K (Kont fs Return)) = goF n fs
    
    go _ _ = Nothing
    
    goF n (Tick _ : fs) = goF n fs
    goF n (Cast _ : fs) = goF n fs
    goF n (App  v : fs) = go n (T v) >>= \n' ->
                          goF n' fs
    goF n []            = Just n
    
    decrement :: Int -> Maybe Int
    decrement 0 = Nothing
    decrement n = Just (n-1)

-- see GHC CoreUtils.lhs
dupAppSize :: Int
dupAppSize = 8

makeTrivial :: TopLevelFlag -> SimplEnv -> OutTerm -> SimplM (SimplEnv, OutTerm)
-- Binds the expression to a variable, if it's not trivial, returning the variable
makeTrivial top_lvl env term = makeTrivialWithInfo top_lvl env vanillaIdInfo term

makeTrivialFrame :: TopLevelFlag -> SimplEnv -> OutFrame -> SimplM (SimplEnv, OutFrame)
makeTrivialFrame top_lvl env frame
  = case frame of App arg -> second App <$> makeTrivial top_lvl env arg
                  other   -> return (env, other)

makeTrivialWithInfo :: TopLevelFlag -> SimplEnv -> IdInfo
                    -> OutTerm -> SimplM (SimplEnv, OutTerm)
-- Propagate strictness and demand info to the new binder
-- Note [Preserve strictness when floating coercions]
-- Returned SimplEnv has same substitution as incoming one
makeTrivialWithInfo top_lvl env info term
  | isTrivialTerm term                          -- Already trivial
  || not (bindingOk top_lvl term term_ty)       -- Cannot trivialise
                                                --   See Note [Cannot trivialise]
  = return (env, term)
  | otherwise           -- See Note [Take care] below
  = do  { uniq <- getUniqueM
        ; let name = mkSystemVarName uniq (fsLit "a")
              var = mkLocalIdWithInfo name term_ty info
        ; env'  <- completeNonRecOut env top_lvl False var var term
        ; expr' <- simplVar env' var
        ; return (env', expr') }
        -- The simplVar is needed becase we're constructing a new binding
        --     a = rhs
        -- And if rhs is of form (rhs1 |> co), then we might get
        --     a1 = rhs1
        --     a = a1 |> co
        -- and now a's RHS is trivial and can be substituted out, and that
        -- is what completeNonRecX will do
        -- To put it another way, it's as if we'd simplified
        --    let var = e in var
  where
    term_ty = termType term

bindingOk :: TopLevelFlag -> SeqCoreTerm -> Type -> Bool
-- True iff we can have a binding of this expression at this level
-- Precondition: the type is the type of the expression
bindingOk top_lvl _ term_ty
  | isTopLevel top_lvl = not (isUnLiftedType term_ty)
  | otherwise          = True

