{-# LANGUAGE ParallelListComp, TupleSections, ViewPatterns, MultiWayIf, CPP #-}

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
import Coercion    ( coercionKind, isCoVar, mkCoCast, mkSymCo )
import CoreMonad   ( Plugin(..), SimplifierMode(..), Tick(..), CoreToDo(..),
                     CoreM, defaultPlugin, reinitializeGlobals,
                     isZeroSimplCount, pprSimplCount, simplCountN,
                     putMsg,
                     getHscEnv, getRuleBase
                   )
import CoreSyn     ( CoreVect(..), CoreRule(..), UnfoldingSource(..)
                   , evaldUnfolding
                   , isRuntimeVar, isStableSource
                   , tickishCounts
                   , ruleArity )
import DataCon
import Demand      ( StrictSig(..), dmdTypeDepth )
import DynFlags    ( DynFlags, DumpFlag(..), GeneralFlag(..)
                   , gopt, dopt
                   , printInfoForUser
                   , ufKeenessFactor, ufUseThreshold )
import ErrUtils    ( dumpSDoc )
import FamInstEnv
import FastString
import Id
import IdInfo      ( IdInfo, demandInfo, strictnessInfo, vanillaIdInfo,
                     setArityInfo, setDemandInfo, setStrictnessInfo, zapDemandInfo )
import HscTypes    ( ExternalPackageState(..), ModGuts(..), VectInfo(..)
                   , hscEPS )
import Literal     ( litIsDupable, litIsLifted )
import Maybes      ( whenIsJust )
import MkCore      ( mkWildValBinder )
import MonadUtils
import Name        ( isExternalName, mkSystemVarName )
import Outputable
import Pair
import qualified PprCore as Core
import Rules       ( extendRuleBaseList, lookupRule, unionRuleBase )
import Type hiding ( extendTvSubst, substTy, substTyVar )
import TysWiredIn  ( mkTupleTy )
import UniqSupply
import Util        ( debugIsOn )
import VarEnv
import VarSet

import Control.Arrow       ( second )
import Control.Exception   ( assert )
import Control.Monad       ( foldM, when )

import Data.List           ( mapAccumL )
import Data.Maybe          ( catMaybes, isJust, mapMaybe )

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

  -- Useful for tracing: Use built-in simplifier until after strictness
  {-
  replace = snd . go False
    where
      go True (CoreDoSimplify max mode : todos)
        = let (b', todos') = go True todos
              in (b', newPass max mode : todos')
      go _ (CoreDoStrictness : todos)
        = let (b', todos') = go True todos
          in (b', CoreDoStrictness : todos')
      go b (CoreDoPasses todos1 : todos2)
        = let (b', todos1') = go b todos1
              (b'', todos2') = go b' todos2
          in (b'', CoreDoPasses todos1' : todos2')
      go b (todo : todos)
        = let (b', todos') = go b todos
          in (b', todo : todos')
      go b []
        = (b, [])
  -}

  newPass max mode
    = CoreDoPluginPass "SeqSimpl" (runSimplifier (max*2) mode)

runSimplifier :: Int -> SimplifierMode -> ModGuts -> CoreM ModGuts
runSimplifier iters mode guts
  = do
    when (tracing || dumping) $ putMsg  $ text "RUNNING SEQUENT CORE SIMPLIFIER"
                                       $$ text "Mode:" <+> ppr mode
    let coreBinds = mg_binds guts
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
    famEnvs = mg_fam_inst_env guts
    
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
        hscEnv <- getHscEnv
        eps <- liftIO $ hscEPS hscEnv
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
            rule_base1 = unionRuleBase ruleBase (eps_rule_base eps)
            rule_base2 = extendRuleBaseList rule_base1 rules
            famEnvs2 = (eps_fam_inst_env eps, famEnvs)
            env = initialEnv dflags mode rule_base2 famEnvs2
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
      
-----------
-- Binds --
-----------

simplModule :: SimplEnv -> [InBind] -> SimplM [OutBind]
simplModule env0 binds0
  = do  {       -- Put all the top-level binders into scope at the start
                -- so that if a transformation rule has unexpectedly brought
                -- anything into scope, then we don't get a complaint about that.
                -- It's rather as if the top-level binders were imported.
                -- See note [Glomming] in OccurAnal.
        ; let (env1, _) = enterRecScopes env0 (bindersOfBinds binds0)
        ; dflags <- getDynFlags
        ; let dump_flag = dopt Opt_D_verbose_core2core dflags
        ; env2 <- simpl_binds dump_flag env1 binds0
        ; freeTick SimplifierDone
        ; return $ getFloatBinds (getFloats env2) }
  where
        -- We need to track the zapped top-level binders, because
        -- they should have their fragile IdInfo zapped (notably occurrence info)
        -- That's why we run down binds and bndrs' simultaneously.
        --
        -- The dump-flag emits a trace for each top-level binding, which
        -- helps to locate the tracing for inlining and rule firing
    simpl_binds :: Bool -> SimplEnv -> [InBind] -> SimplM SimplEnv
    simpl_binds _    env []           = return env
    simpl_binds dump env (bind:binds) = do { env' <- trace_bind dump bind $
                                                     simpl_bind env bind
                                           ; simpl_binds dump env' binds }

    trace_bind True  bind = pprTrace "SimplBind" (ppr (bindersOf bind))
    trace_bind False _    = \x -> x

    simpl_bind env (Rec pairs)   = simplRec          env  pairs TopLevel
    simpl_bind env (NonRec pair) = simplRecOrTopPair env' b b' r TopLevel NonRecursive
        where
          (b, r) = destBindPair pair
          (env', b') = addBndrRules env b (lookupRecBndr env b)

{-
simplNonRecInCommand is used for
  * [simplCommand] non-top-level non-recursive lets in commands
  * [simplTermInCommand] beta reduction
  
These two call sites are different enough to need different metacontinuations
(StrictLet and StrictLamBind, respectively). Since simplNonRecInCommand doesn't
know which one called, the caller needs to say what metacontinuation to use in
case the binding is strict and we tail-recurse into the right-hand side.
-}
-- c.f. Simplify.simplNonRecE
simplNonRecInCommand :: SimplEnv -> InVar -> StaticEnv -> InRhs
                     -> MetaKont
                        -- ^ MetaKont to recurse with if strict
                     -> (SimplEnv -> SimplM (SimplEnv, OutCommand))
                        -- ^ Continuation to call if lazy or pre-inlined
                     -> SimplM (SimplEnv, OutCommand)
simplNonRecInCommand env_x x env_v rhs mk_strict _
  | tracing
  , pprTraceShort "simplNonRecInCommand" (ppr env_x $$ ppr x $$ ppr env_v $$ ppr rhs $$ ppr mk_strict) False
  = undefined
simplNonRecInCommand env_x x env_v rhs _mk_strict k_lazy
  | isTyVar x
  , Left (Type ty) <- rhs
  = let ty' = substTy (env_v `inDynamicScope` env_x) ty
    in k_lazy $ extendTvSubst env_x x ty'
  | isTyVar x
  = pprPanic "simplNonRec" (ppr x <+> ppr rhs)
simplNonRecInCommand env_x x env_v rhs mk_strict k_lazy
  = do
    preInline <- preInlineUnconditionally env_x env_v (mkBindPair x rhs) NotTopLevel
    case () of 
      _ | preInline
       -> do
          tick (PreInlineUnconditionally x)
          let ans = Susp env_v rhs
              env' = extendIdOrPvSubst env_x x ans
          k_lazy env'
        | isStrictId x
        , Left term <- rhs -- A join point could be marked strict by happenstance,
                           -- but it's hard to see what the meaning would be here
       -> do
          let env       = env_v `inDynamicScope` env_x
              (env', _) = enterKontScope env BoringCtxt (idType x)
              env_rhs   = env' `setRetKont` mk_strict
          simplTermInCommand env_rhs term Nothing []
                             (Incoming (staticPart env_rhs) Return)
        | otherwise
       -> do
          let (env_x',  x')  = enterScope env_x x
              (env_x'', x'') = addBndrRules env_x' x x'
          env_final <- simplLazyOrPKontBind env_x'' x x'' env_v rhs
                                            NotTopLevel NonRecursive
          k_lazy env_final

{-
simplRecOrTopPair is used for
        * recursive bindings (whether top level or not)
        * top-level non-recursive bindings

It assumes the binder has already been simplified, but not its IdInfo.
-}

simplRecOrTopPair :: SimplEnv
                  -> InId -> OutBndr -> InRhs
                  -> TopLevelFlag -> RecFlag
                  -> SimplM SimplEnv
simplRecOrTopPair env old_bndr new_bndr rhs top_lvl is_rec
  = do -- Check for unconditional inline
       preInline <- preInlineUnconditionally env (staticPart env) (mkBindPair old_bndr rhs) top_lvl
       if preInline
           then do tick (PreInlineUnconditionally old_bndr)
                   return $ extendIdOrPvSubst env old_bndr (Susp (staticPart env) rhs)
           else simplLazyOrPKontBind env old_bndr new_bndr (staticPart env) rhs top_lvl is_rec

simplLazyOrPKontBind :: SimplEnv -> InVar -> OutVar -> StaticEnv -> InRhs -> TopLevelFlag
                     -> RecFlag -> SimplM SimplEnv
simplLazyOrPKontBind env_x x x' env_r r level recFlag
  = case r of
      Left term -> assert (not (isPKontId x)) $
                   simplLazyBind env_x x x' env_r term level recFlag
      Right pk  -> assert (isPKontId x && isNotTopLevel level) $ do
                   env_r' <- ensureDupableKont (env_r `inDynamicScope` zapFloats env_x)
                     -- Note [Call ensureDupableKont around join point]
                   simplPKontBind (env_x `addFloats` env_r') x x' (staticPart env_r') pk recFlag

{-
simplLazyBind is used for
  * [simplRecOrTopPair] recursive bindings (whether top level or not)
  * [simplRecOrTopPair] top-level non-recursive bindings
  * [simplNonRec]      non-top-level *lazy* non-recursive bindings

Nota bene:
    1. It assumes that the binder is *already* simplified,
       and is in scope, and its IdInfo too, except unfolding

    2. It assumes that the binder type is lifted.

    3. It does not check for pre-inline-unconditionallly;
       that should have been done already.
-}

simplLazyBind :: SimplEnv -> InVar -> OutVar -> StaticEnv -> InTerm -> TopLevelFlag
              -> RecFlag -> SimplM SimplEnv
simplLazyBind env_x x x' env_v v level recFlag
  | tracing
  , pprTraceShort "simplLazyBind" (ppr x <+> (if x == x' then empty else darrow <+> ppr x')
                                      <+> ppr level <+> ppr recFlag $$ pprBndr LetBind x' $$ ppr v) False
  = undefined
  | isCoVar x
  , Coercion co <- assert (isCoArg v) v
  = let co' = simplCoercion (env_v `inDynamicScope` env_x) co
    in return $ extendCvSubst env_x x co'
  | otherwise
  = do
    -- TODO Handle floating type lambdas
    let env_v' = zapFloats (env_v `inDynamicScope` env_x)
    (env_v'', v') <- simplTerm env_v' RhsCtxt v
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
                     -- The situation: We have
                     --     x = compute < term | fs; cast co; ret >
                     -- We will call makeTrivial on < term | fs; ret >. Typically
                     -- this will generate
                     --     x' = compute < term | fs; ret >
                     -- thus giving us
                     --     compute < x' | cast co; ret >
                     -- as the new RHS for x.
                     --
                     -- Note that we already know what the strictness and demand
                     -- of x' should be - namely those of x. So we propagate
                     -- some of the idInfo over.
                     let Pair fromTy _toTy = coercionKind co
                         rhs' = mkCompute fromTy (Eval term (Kont fs' Return))
                         info = idInfo x
                         sanitizedInfo = vanillaIdInfo `setStrictnessInfo` strictnessInfo info
                                                       `setDemandInfo` demandInfo info
                     (env'', rhs'') <- makeTrivialWithInfo level env' sanitizedInfo rhs'
                     return (env'', mkCast rhs'' co)
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

{-
simplPKontBind is used for
  * [simplRecOrTopPair] recursive pkont bindings
  * [simplNonRec]       non-recursive pkont bindings

Nota bene:
    1. It assumes that the binder is *already* simplified,
       and is in scope, and its IdInfo too, except unfolding

    2. It does not check for pre-inline-unconditionallly;
       that should have been done already.
-}
simplPKontBind :: SimplEnv -> InPKontId -> OutPKontId -> StaticEnv -> InPKont
               -> RecFlag -> SimplM SimplEnv
simplPKontBind _env_j j j' _env_pk pk recFlag
  | tracing
  , pprTraceShort "simplPKontBind" (ppr j <+> (if j == j' then empty else darrow <+> ppr j') <+>
                                    ppr recFlag $$ ppr pk) False
  = undefined
simplPKontBind env_j j j' env_pk pk _recFlag
  = do
    let env_pk' = zapFloats (env_pk `inDynamicScope` env_j)
    (env_with_floats, pk') <- simplPKont env_pk' pk
    env_j' <-
      if isEmptyFloats env_with_floats
         then    return env_j
         else do tick LetFloatFromLet -- Can always float through a cont binding
                                      -- (If the cont has parameters, the floats
                                      -- won't make it here; see simplPKont.)
                 return $ env_j `addFloats` env_with_floats
    completeBind env_j' j j' (Right pk') NotTopLevel

{-
Note [Call ensureDupableKont outside join point]

We need to make sure we call ensureDupableKont whenever the same binding of ret,
the return continuation, appears in two places. When there are no join points in
scope, we can just wait until we see a multi-branch case, but join points make
this trickier: A ret inside a join point might be the only occurrence, but maybe
not. One solution would be to leverage the occurrence analyzer: It could count
the rets just like any other name, and we could add an OccInfo (or a placeholder
binder) to the Compute constructor to hold it. For the time being, we assume
that any join point needs the continuation to be duplicable. At worst, this
might cause an extra iteration if mkDupableKont creates bindings that are only
used once.
-}

simplPKont :: SimplEnv -> InPKont -> SimplM (SimplEnv, OutPKont)
simplPKont env pk
  = case pk of
      -- Can only float bindings out if there are no parameters
      PKont [] comm -> do
        (env', comm') <- simplCommand env comm
        return (env', PKont [] comm')
      _ -> do
        pk' <- simplPKontNoFloats env pk
        return (env, pk')

simplPKontNoFloats :: SimplEnv -> InPKont -> SimplM OutPKont
simplPKontNoFloats env (PKont xs comm)
  = do
    let (env', xs') = enterLamScopes env xs
    comm' <- simplCommandNoFloats env' comm
    return $ PKont xs' comm'

simplRhsNoFloats :: SimplEnv -> InRhs -> SimplM OutRhs
simplRhsNoFloats env (Left term) = Left  <$> simplTermNoFloats  env RhsCtxt term
simplRhsNoFloats env (Right pk)  = Right <$> simplPKontNoFloats env pk

completeBind :: SimplEnv -> InVar -> OutVar -> OutRhs
             -> TopLevelFlag -> SimplM SimplEnv
completeBind env x x' v level
  | isCoVar x
  = case v of
      Left (Coercion co) -> return (extendCvSubst env x co)
      Right _            -> pprPanic "completeBind" (ppr x <+> ppr v)
      _                  -> return (addNonRecFloat env (mkBindPair x' v))
  | otherwise
  = do
    (newArity, v') <- tryEtaExpandRhs env x' v
    let oldDef = findDef env x
    newDef <- simplDef env level x v' oldDef
    postInline <- postInlineUnconditionally env (mkBindPair x v') level newDef
    if postInline
      then do
        tick (PostInlineUnconditionally x)
        -- Nevermind about substituting x' for x; we'll substitute v' instead
        return $ extendIdOrPvSubst env x (Done v')
      else do
        let def = mkDef env level v'
            info1 = idInfo x' `setArityInfo` newArity
            (env', x'') = setDef env (x' `setIdInfo` info1) def
            info2 = idInfo x''
              -- Demand info: Note [Setting the demand info] in GHC Simplify
              --
              -- We also have to nuke demand info if for some reason
              -- eta-expansion *reduces* the arity of the binding to less
              -- than that of the strictness sig. This can happen: see Note [Arity decrease].
            info3 | defIsEvald def
                    || (case strictnessInfo info2 of
                          StrictSig dmd_ty -> newArity < dmdTypeDepth dmd_ty)
                  = zapDemandInfo info2 `orElse` info2
                  | otherwise
                  = info2
            x_final = x' `setIdInfo` info3
        
        when tracing $ liftCoreM $ putMsg (text "defined" <+> ppr x_final <+> equals <+> ppr def)
        return $ addNonRecFloat env' (mkBindPair x_final v')

-- (from Simplify.simplUnfolding)
------------------------------
simplDef :: SimplEnv -> TopLevelFlag
         -> InId
         -> OutRhs
         -> Definition -> SimplM Definition
-- Note [Setting the new unfolding]
simplDef env top_lvl id new_rhs def
  = case def of
      BoundToDFun { dfun_bndrs = bndrs, dfun_dataCon = con, dfun_args = args }
        -> do { let (env', bndrs') = enterLamScopes rule_env bndrs
              ; args' <- mapM (simplTermNoFloats env' BoringCtxt) args
              ; return (mkBoundToDFun bndrs' con args') }

      BoundTo { def_rhs = rhs, def_arity = arity
              , def_src = src, def_guidance = guide }
        | isStableSource src
        -> do { rhs' <- simplRhsNoFloats rule_env rhs
              ; case guide of
                  Usually {}   -- Happens for INLINE things
                     -> let guide' = guide { guEvenIfBoring = inlineBoringOk rhs' }
                        -- Refresh the boring-ok flag, in case expr'
                        -- has got small. This happens, notably in the inlinings
                        -- for dfuns for single-method classes; see
                        -- Note [Single-method classes] in TcInstDcls.
                        -- A test case is Trac #4138
                        in return (mkBoundToWithGuidance env rhs' src top_lvl arity guide')
                            -- See Note [Top-level flag on inline rules] in CoreUnfold

                  _other              -- Happens for INLINABLE things
                     -> bottoming `seq` -- See Note [Force bottoming field]
                        do { let dflags = dynFlags env
                           ; return (mkBoundTo env dflags rhs' src top_lvl bottoming) } }
                -- If the guidance is UnfIfGoodArgs, this is an INLINABLE
                -- unfolding, and we need to make sure the guidance is kept up
                -- to date with respect to any changes in the unfolding.

      _other -> bottoming `seq`
                do { let dflags = dynFlags env
                   ; return (mkBoundTo env dflags new_rhs InlineRhs top_lvl bottoming) }
                     -- We make an  unfolding *even for loop-breakers*.
                     -- Reason: (a) It might be useful to know that they are WHNF
                     --         (b) In TidyPgm we currently assume that, if we want to
                     --             expose the unfolding then indeed we *have* an unfolding
                     --             to expose.  (We could instead use the RHS, but currently
                     --             we don't.)  The simple thing is always to have one.
  where
    bottoming = isBottomingId id
    act      = idInlineActivation id
    rule_env = updMode (updModeForInlineRules act) env
               -- See Note [Simplifying inside InlineRules] in SimplUtils

updModeForInlineRules :: Activation -> SimplifierMode -> SimplifierMode
-- See Note [Simplifying inside InlineRules]
updModeForInlineRules inline_rule_act current_mode
  = current_mode { sm_phase = phaseFromActivation inline_rule_act
                 , sm_inline = True
                 , sm_eta_expand = False }
                 -- For sm_rules, just inherit; sm_rules might be "off"
                 -- because of -fno-enable-rewrite-rules
  where
    phaseFromActivation (ActiveAfter n) = Phase n
    phaseFromActivation _               = InitialPhase

tryEtaExpandRhs :: SimplEnv -> OutId -> OutRhs -> SimplM (Arity, OutRhs)
tryEtaExpandRhs env x (Left v)
  = do (arity, v') <- tryEtaExpandRhsTerm env x v
       return (arity, Left v')
tryEtaExpandRhs _ _ (Right pk@(PKont xs _))
  = return (length (filter isId xs), Right pk)
      -- TODO Somehow take into account the arity of the outer context

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
    def <- simplDef env level (binderOfPair pair) (rhsOfPair pair) NoDefinition
    let (env', x') = setDef env (binderOfPair pair) def
    return $ addNonRecFloat env' (pair `setPairBinder` x')
addPolyBind env _level bind@(Rec _)
  -- Be conservative like the original simplifier here; recursiveness is tricky
  -- (worst case is we cause extra iteration by not updating definitions now)
  = return $ extendFloats env bind

simplRec :: SimplEnv
         -> [InBindPair] -- but binders *already in scope*
         -> TopLevelFlag
         -> SimplM SimplEnv
simplRec env0 pairs0 top_lvl
  = do  { let (env_with_info, triples) = mapAccumL add_rules env0 pairs0
        ; env1 <- go (zapFloats env_with_info) triples
        ; return (env0 `addRecFloats` env1) }
        -- addFloats adds the floats from env1,
        -- _and_ updates env0 with the in-scope set from env1
  where
    add_rules :: SimplEnv -> InBindPair -> (SimplEnv, (InBndr, OutBndr, InRhs))
        -- Add the (substituted) rules to the binder
    add_rules env (destBindPair -> (bndr, rhs)) = (env', (bndr, bndr', rhs))
        where
          (env', bndr') = addBndrRules env bndr (lookupRecBndr env bndr)

    go env [] = return env

    go env ((old_bndr, new_bndr, rhs) : pairs)
        = do { env' <- simplRecOrTopPair env old_bndr new_bndr rhs top_lvl Recursive
             ; go env' pairs }

-----------------
-- Expressions --
-----------------

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
simplCommand env (Let (Rec pairs) comm)
  = do
    let (env', _) = enterRecScopes env (map binderOfPair pairs)
    env'' <- simplRec env' pairs NotTopLevel
    simplCommand env'' comm
simplCommand env (Let (NonRec pair) comm)
  = do
    let (x, rhs) = destBindPair pair
        stat = staticPart env
        -- If the binding is strict, we tail-recurse into the term, so we need
        -- a metacontinuation to resume
        mk = StrictLet { mk_env = stat
                       , mk_binder = x
                       , mk_command = comm }
    simplNonRecInCommand env x (staticPart env) rhs mk $
      \env' -> simplCommand env' comm
simplCommand env (Eval term (Kont fs end))
  = simplTermInCommand env term Nothing (map (Incoming stat) fs) (Incoming stat end)
  where
    stat = staticPart env
simplCommand env (Jump args j)
  = simplJump env args j

simplTermNoFloats :: SimplEnv -> CallCtxt -> InTerm -> SimplM OutTerm
simplTermNoFloats env ctxt (Compute ty comm)
  = do
    let (env', ty') = enterKontScope env ctxt ty
    comm' <- simplCommandNoFloats env' comm
    return $ mkCompute ty' comm'
simplTermNoFloats env ctxt term
  = do
    (env', term') <- simplTerm (zapFloats env) ctxt term
    return $ wrapFloatsAroundTerm env' term'

simplTerm :: SimplEnv -> CallCtxt -> InTerm -> SimplM (SimplEnv, OutTerm)
simplTerm env _ctxt (Type ty)
  = return (env, Type (substTy env ty))
simplTerm env _ctxt (Coercion co)
  = return (env, Coercion (simplCoercion env co))
simplTerm env ctxt (Compute ty comm)
  = do
    let (env', ty') = enterKontScope env ctxt ty
    -- Terms are closed with respect to continuation variables, so they can
    -- safely float past this binder. Continuations must *never* float past it,
    -- however, because they necessarily invoke the continuation bound here.
    (env'', comm') <- simplCommandNoKontFloats (zapFloats env') comm
    return (env `addFloats` env'', mkCompute ty' comm')
simplTerm env ctxt v
  = do
    let (env', ty') = enterKontScope env ctxt ty
        env'' = zapFloats env'
    (env''', comm) <- simplTermInCommand env'' v Nothing [] (Incoming (staticPart env'') Return)
    return (env, mkCompute ty' (wrapFloats env''' comm))
  where ty = substTy env (termType v)

{-
Note [Main simplifier loop]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Most interesting terms go through the following sequence of mutually
tail-recursive functions. There are a few more in between, but these are the
most important steps.

simplTermInCommand     :: SimplEnv -> InTerm -> Maybe SubstedCoercion
                       -> [ScopedFrame] -> ScopedEnd
                       -> SimplM (SimplEnv, OutCommand)

Simplifies the term, based on its unsimplified context. Inlining and
beta-reduction apply here, as does entering Compute terms.

simplTermInCommandDone :: SimplEnv -> OutTerm -> Maybe SubstedCoercion
                       -> [ScopedFrame] -> ScopedEnd
                       -> SimplM (SimplEnv, OutCommand)

Called when simplTermInCommand finishes. Packages up the term and the (possible)
coercion to build the initial ArgInfo, then continues onto simplKont.

simplKont              :: SimplEnv -> ArgInfo
                       -> [ScopedFrame] -> ScopedEnd
                       -> SimplM (SimplEnv, OutCommand)

Simplifies the continuation, going frame by frame and then processing the end.
Each frame may interrupt the flow by going into a strict argument, which pulls
the whole state into a StrictArg metacontinuation before jumping into the
argument. After a frame is processed, it is added to the ArgInfo, whose
ai_frames field acts as an accumulator. Rewrite rules fire in between the frames
and the end.

invokeMetaKont         :: SimplEnv -> OutTerm
                       -> SimplM (SimplEnv, OutCommand)

Pulls the metacontinuation from the environment, if any, and invokes it. This
may resume an earlier loop from where a strict argument was found.

simplKontDone          :: SimplEnv -> OutTerm -> OutEnd
                       -> SimplM (SimplEnv, OutCommand)

Called at the very end, either when a Return is encountered with no bound
metacontinuation or after all the branches of a Case are recursed into. Attaches
the Term to the End and returns.
-}

simplTermInCommand     :: SimplEnv -> InTerm -> Maybe SubstedCoercion
                       -> [ScopedFrame] -> ScopedEnd
                       -> SimplM (SimplEnv, OutCommand)
simplTermInCommand env_v v co_m fs end
  | tracing
  , pprTraceShort "simplTermInCommand" (
      ppr env_v $$ ppr v $$ maybe empty showCo co_m $$ pprMultiScopedKont fs end
    ) False
  = undefined
  where
    showCo co = text "coercing:" <+> ppr fromTy <+> darrow <+> ppr toTy
      where Pair fromTy toTy = coercionKind co
simplTermInCommand _ (Type ty) _ _ _
  = pprPanic "simplTermInCommand" (ppr ty)
simplTermInCommand env_v v co_m fs end
  -- If end is Return and its scope has a syntactic continuation, pull it in now
  | (env', Return) <- openScoped env_v end
  , Just (SynKont { mk_frames = fs', mk_end = end' }) <- substKv env'
  = simplTermInCommand env_v v co_m (fs ++ fs') end'
simplTermInCommand env_v (Var x) co_m fs end
  = case substId env_v x of
      DoneId x'
        -> do
           let lone | (unScope -> App {}) : _ <- fs = False
                    | otherwise                     = True
               term'_maybe = callSiteInline env_v x' (activeUnfolding env_v x')
                                            lone fs end
           case term'_maybe of
             Nothing
               -> simplTermInCommandDone env_v (Var x') co_m fs end
             Just (Left term')
               -> do
                  tick (UnfoldingDone x')
                  dump_inline (dynFlags env_v) term' fs end
                  simplTermInCommand (zapSubstEnvs env_v) term' co_m fs end
             _ -> pprPanic "simplTermInCommand" (ppr x $$ ppr term'_maybe)
      Done v
        -- Term already simplified (then PostInlineUnconditionally'd), so
        -- don't do any substitutions when processing it again
        -> simplTermInCommand (zapSubstEnvs env_v) v co_m fs end
      Susp stat v
        -> simplTermInCommand (env_v `setStaticPart` stat) v co_m fs end
  where
    dump_inline dflags def fs end
      | not (tracing || dopt Opt_D_dump_inlinings dflags) = return ()
      | not (tracing || dopt Opt_D_verbose_core2core dflags)
      = when (isExternalName (idName x)) $
            liftIO $ printInfoForUser dflags alwaysQualify $
                sep [text "Inlining done:", nest 4 (ppr x)]
      | otherwise
      = liftIO $ printInfoForUser dflags alwaysQualify $
           sep [text "Inlining done: " <> ppr x,
                nest 4 (vcat [text "Inlined fn: " <+> nest 2 (ppr def),
                              text "Cont:  " <+> pprMultiScopedKont fs end])]

simplTermInCommand env_v (Compute ty c) co_m fs end
  = do
    let (env_v', _) = enterKontScope env_v (getContext env_v) ty
        fs'         | Just co <- co_m
                    = Simplified NoDup Nothing (Cast co) : fs
                    | otherwise = fs
        env_c       = env_v' `setRetKont` SynKont { mk_dup    = NoDup
                                                  , mk_frames = fs'
                                                  , mk_end    = end }
    simplCommand env_c c
simplTermInCommand env_v v co_m (f : fs) end
  | (env', Cast co) <- openScoped env_v f
  = simplTermInCommand env_v v (combineCo co_m (substCo env' co)) fs end
simplTermInCommand env_v (Coercion co) co_m fs end
  = simplTermInCommandDone env_v v' Nothing fs end
  where
    co' = simplCoercion env_v co
    v' = case co_m of
           Just coCo -> Coercion (mkCoCast coCo co')
           Nothing   -> Coercion co'
simplTermInCommand env_v v@(Lam x body) co_m (f : fs) end
  -- discard a non-counting tick on a lambda.  This may change the
  -- cost attribution slightly (moving the allocation of the
  -- lambda elsewhere), but we don't care: optimisation changes
  -- cost attribution all the time. (comment from Simplify.simplLam)
  | Tick ti <- f'
  , not (tickishCounts ti)
  = simplTermInCommand env_v v co_m fs end
  | App arg <- f'
  = do
    tick (BetaReduction x)
    let (arg', co_m', env_k')
          | Just co <- co_m = let -- Substitute now because arg is InTerm and
                                  -- co is SubstedCoercion
                                  arg_substed = substTerm (text "simplTermInCommand")
                                                          env_k arg
                                  Just (arg', co') = castApp arg_substed co
                                    -- castApp is not Nothing because lambda must
                                    -- have function/forall type
                              in (arg', Just co', zapSubstEnvs env_k)
          | otherwise       = (arg, Nothing, env_k)
        mk = StrictLamBind { mk_env      = staticPart env_v
                           , mk_context  = getContext env_v
                           , mk_binder   = x
                           , mk_term     = body
                           , mk_coercion = co_m'
                           , mk_frames   = fs
                           , mk_end      = end }
    simplNonRecInCommand env_v x (staticPart env_k') (Left arg') mk $
      \env_v' -> simplTermInCommand env_v' body co_m' fs end
  where
    (env_k, f') = openScoped env_v f
simplTermInCommand env_v term@(Lam {}) co_m fs end
  = do
    let (xs, body) = lambdas term
        (env_v', xs') = enterLamScopes env_v xs
    body' <- simplTermNoFloats env_v' BoringCtxt body
    term' <- mkLam env_v xs' body'
    simplTermInCommandDone env_v term' co_m fs end
simplTermInCommand env_v term@(Lit {}) co_m fs end
  = simplTermInCommandDone env_v term co_m fs end

simplTermInCommandDone :: SimplEnv -> OutTerm -> Maybe SubstedCoercion
                       -> [ScopedFrame] -> ScopedEnd
                       -> SimplM (SimplEnv, OutCommand)

simplTermInCommandDone env_v v co_m fs end
  = simplKont env_v (mkArgInfo env_v v co_m fs end) fs end

{-
Note [simplKont invariants]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

simplKont is used in two rather different situations:
  1. Simplifying the continuation in an Eval command (then possibly invoking rules)
  2. Simplifying the arguments to a jump

The ArgInfo contains a "target" that identifies the case: In case 1, the target
is a TermTarget with the term on the left of the command, and in case 2, the
target identifies a parameterized continuation (either by its body or by its
name).

As a jump has a very specific form, case 2 has some invariants:
  - All the frames are App frames, and there are exactly as many as the arity
    of the join point
  - The end is a Return
-}

simplKont :: SimplEnv -> ArgInfo
          -> [ScopedFrame] -> ScopedEnd
          -> SimplM (SimplEnv, OutCommand)
simplKont env ai fs end
  | tracing
  , pprTraceShort "simplKont" (
      ppr env $$ ppr ai $$ pprMultiScopedKont fs end
    ) False
  = undefined
simplKont env (ai@ArgInfo { ai_strs = [] }) fs end
  -- We've run out of strictness arguments, meaning the call is definitely bottom
  | not (null fs && isReturn (unScope end)) -- Don't bother throwing away a trivial continuation
  = simplKontDone env term (Case (mkWildValBinder ty) []) -- Skips invokeMetaKont
  where
    term = argInfoToTerm ai
    ty = termType term
simplKont env ai (Simplified _ _ f : fs) end
  = simplKont env (addFrameToArgInfo ai f) fs end
simplKont env ai (f : fs) end
  = case openScoped env f of
      (env', f') -> simplKontFrame env' ai f' fs end
simplKont env ai [] end
  = case openScoped env end of
      (env', end') -> simplKontEnd env' ai end'

simplKontFrame :: SimplEnv -> ArgInfo
               -> InFrame -> [ScopedFrame] -> ScopedEnd
               -> SimplM (SimplEnv, OutCommand)
simplKontFrame env ai (Cast co) fs end
  = simplKont env (ai { ai_co = ai_co ai `combineCo` substCo env co }) fs end
simplKontFrame env ai f@(App _) fs end
  | Just co <- ai_co ai
  , let Pair fromTy _toTy = coercionKind co
  , Nothing <- splitFunTy_maybe fromTy
  , Nothing <- splitForAllTy_maybe fromTy
  -- Can't push the cast after the arguments, so eat it
  = simplKontFrame env (swallowCoercion ai) f fs end
simplKontFrame env ai (App (Type tyArg)) fs end
  = do
    let ty' = substTy env tyArg
    simplKont env (addFrameToArgInfo ai (App (Type ty'))) fs end
simplKontFrame _ (ArgInfo { ai_discs = [] }) _ _ _
  = pprPanic "simplKontFrame" (text "out of discounts??")
simplKontFrame _ (ArgInfo { ai_strs = [] }) _ _ _
  = pprPanic "simplKontFrame" (text "should have dealt with bottom already")
simplKontFrame env ai@(ArgInfo { ai_strs = str:_
                               , ai_discs = disc:_ }) (App arg) fs end
  | str
  = do
    -- Push the current evaluation state into the environment as a
    -- meta-continuation. We'll continue with the rest of the frames when we
    -- finish simplifying the term. This, of course, reflects left-to-right
    -- call-by-value evaluation.
    let mk = StrictArg { mk_dup = NoDup
                       , mk_argInfo = ai
                       , mk_frames = fs
                       , mk_context = getContext env
                       , mk_end = end }
        (env', _ty') = enterKontScope env cci (termType arg)
        env_final    = env' `setRetKont` mk
    simplCommand env_final (Eval arg (Kont [] Return))
  | otherwise
  = do
    -- Don't float out of lazy arguments (see Simplify.rebuildCall)
    arg_final <- simplTermNoFloats env cci arg
    simplKont env (addFrameToArgInfo ai (App arg_final)) fs end
  where
    cci | ai_encl ai = RuleArgCtxt
        | disc > 0   = DiscArgCtxt
        | otherwise  = BoringCtxt
simplKontFrame env ai (f@(Tick _)) fs end
  -- FIXME Tick handling is actually rather delicate! In fact, we should
  -- (somehow) be putting a float barrier here (see Simplify.simplTick).
  = simplKont env (addFrameToArgInfo ai f) fs end

simplKontEnd :: SimplEnv -> ArgInfo
             -> InEnd
             -> SimplM (SimplEnv, OutCommand)
{-
If simplifying a Jump, rules cannot apply, there cannot be a coercion, the end
must be Return, and the metacontinuation will not be invoked (it is only invoked
by a Return from an actual Eval command). Thus we skip out here.
-}
simplKontEnd env (ArgInfo { ai_target = JumpTarget j, ai_frames = fs }) end
  = assert (isReturn end && all isAppFrame fs) $ -- Note [simplKont invariants]
    return (env, Jump [ arg | App arg <- reverse fs ] j)
simplKontEnd env (ArgInfo { ai_target = PKontTarget pk, ai_frames = fs }) end
  = assert (isReturn end && all isAppFrame fs) $ -- Note [simplKont invariants]
    do
    let (env', PKont xs comm) = openScoped env pk
        args = [ arg | App arg <- reverse fs ]
    env'' <- foldM (\env (x, v) -> simplNonRecOut env x v) env' (zip xs args)
    simplCommand env'' comm
simplKontEnd env ai@(ArgInfo { ai_co = Just _ }) end
  = simplKontEnd env (swallowCoercion ai) end
-- From now on, no coercion
simplKontEnd env ai@(ArgInfo { ai_target = TermTarget (Var fun), ai_rules = rules }) end
  | not (null rules)
  = do
    let (args, extraFrames) = argInfoSpanArgs ai
    match_maybe <- tryRules env rules fun args
    case match_maybe of
      Just (ruleRhs, extraArgs) ->
        let simplFrames = map (Simplified NoDup Nothing) (map App extraArgs ++ extraFrames)
        in simplTermInCommand env ruleRhs Nothing simplFrames (Incoming (staticPart env) end)
      Nothing -> simplKontAfterRules env ai end    
simplKontEnd env ai end
  = simplKontAfterRules env ai end

simplKontAfterRules :: SimplEnv -> ArgInfo
                    -> InEnd
                    -> SimplM (SimplEnv, OutCommand)
simplKontAfterRules _ (ArgInfo { ai_co = Just co }) _
  = pprPanic "simplKontAfterRules" (text "Leftover coercion:" <+> ppr co)
simplKontAfterRules env ai (Case x alts)
  | TermTarget (Lit lit) <- ai_target ai
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
    scrut = assert (argInfoHasTerm ai) $ argInfoToTerm ai
              -- Note [simplKont invariants]
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
      
    scrut = argInfoToTerm ai
simplKontAfterRules env ai (Case x alts)
  = do
    env' <- if length alts > 1
              then ensureDupableKont env -- we're about to duplicate the context
              else return env
    let ai' = swallowCoercion ai
        scrut = argInfoToTerm ai'
    
    (co_m, x', alts') <- simplAlts env' scrut x alts
    let ai'' = case co_m of
                 Just co -> ai' { ai_frames = Cast co : ai_frames ai' }
                 Nothing -> ai'
    dflags <- getDynFlags
    Kont fs' end' <- mkCase dflags x' alts'
    let ai_final = addFramesToArgInfo ai'' fs'
        term_final = argInfoToTerm ai_final
    simplKontDone env' term_final end'
simplKontAfterRules env ai Return
  = invokeMetaKont env (argInfoToTerm ai)

invokeMetaKont :: SimplEnv -> OutTerm
               -> SimplM (SimplEnv, OutCommand)
invokeMetaKont env term
  | tracing
  , Just mk <- substKv env
  , pprTraceShort "invokeMetaKont" (ppr mk $$ ppr term) False
  = undefined
  | otherwise
  = case substKv env of
      Nothing
        -> simplKontDone env term Return
      Just (SynKont { mk_frames = fs, mk_end = end })
        -> warnPprTrace True __FILE__ __LINE__
             (text "SynKont lasted until invokeMetaKont" $$ ppr env $$ ppr term) $
             simplTermInCommand env term Nothing fs end
      Just (StrictArg { mk_argInfo = ai'
                      , mk_frames = fs
                      , mk_end = end
                      , mk_context = ctxt })
        -> simplKont (env `setContext` ctxt) (addFrameToArgInfo ai' (App term)) fs end
      Just (StrictLet { mk_env = stat
                      , mk_binder = bndr
                      , mk_command = comm })
        -> do
           env' <- simplNonRecOut (stat `inDynamicScope` env) bndr term
           let env_final = env' `setContext` BoringCtxt
           simplCommand env_final comm
      Just (StrictLamBind { mk_env = stat
                          , mk_binder = bndr
                          , mk_term = body
                          , mk_coercion = co_m
                          , mk_frames = fs
                          , mk_end = end
                          , mk_context = ctxt })
        -> do
           env' <- simplNonRecOut (stat `inDynamicScope` env) bndr term
           let env_final = env' `setContext` ctxt
           simplTermInCommand env_final body co_m fs end

simplKontDone :: SimplEnv -> OutTerm -> OutEnd
              -> SimplM (SimplEnv, OutCommand)
simplKontDone env term end
  | tracing
  , pprTraceShort "simplKontDone" (ppr env $$ ppr term $$ ppr end) False
  = undefined
  | Compute _ (Eval term' (Kont fs Return)) <- term
      -- Common code path: simplKontAfterRules -> invokeKont -> simplKontDone
  = return (env, Eval term' (Kont fs end))
  | otherwise
  = return (env, mkCommand [] term (Kont [] end))

-------------------
-- Case handling --
-------------------

simplAlts :: SimplEnv -> OutTerm -> InId -> [InAlt]
          -> SimplM (Maybe OutCoercion, OutId, [OutAlt])
simplAlts env scrut case_bndr alts
  = do  { let env0 = zapFloats env

        ; let (env1, case_bndr1) = enterScope env0 case_bndr

        ; let fam_envs = getFamEnvs env1
        ; (alt_env', co_m, case_bndr') <- improveSeq fam_envs env1
                                                     case_bndr case_bndr1 alts
        ; let scrut' = case co_m of
                         Just co -> mkCast scrut co
                         Nothing -> scrut
        ; (imposs_deflt_cons, in_alts) <- prepareAlts scrut' case_bndr' alts
          -- NB: it's possible that the returned in_alts is empty: this is handled
          -- by the caller (rebuildCase) in the missingAlt function

        ; alts' <- mapM (simplAlt alt_env' (Just scrut') imposs_deflt_cons case_bndr') in_alts
        ; -- pprTrace "simplAlts" (ppr case_bndr $$ ppr alts_ty $$ ppr alts_ty' $$ ppr alts $$ ppr cont') $
          return (co_m, case_bndr', alts') }

improveSeq :: (FamInstEnv, FamInstEnv) -> SimplEnv
           -> InId -> OutId -> [InAlt]
           -> SimplM (SimplEnv, Maybe OutCoercion, OutId)
-- Note [Improving seq] in GHC's Simplify
improveSeq fam_envs env case_bndr case_bndr1 [Alt DEFAULT _ _]
  | not (isDeadBinder case_bndr) -- Not a pure seq!  See Note [Improving seq]
  , Just (co, ty2) <- topNormaliseType_maybe fam_envs (idType case_bndr1)
  = do { case_bndr2 <- mkSysLocalM (fsLit "nt") ty2
        ; let rhs  = Done (mkCast (Var case_bndr2) (mkSymCo co))
              env2 = extendIdSubst env case_bndr rhs
        ; return (env2, Just co, case_bndr2) }

improveSeq _ env _ case_bndr1 _
  = return (env, Nothing, case_bndr1)

simplAlt :: SimplEnv -> Maybe OutTerm -> [AltCon] -> OutId -> InAlt -> SimplM OutAlt
simplAlt env _ notAmong caseBndr (Alt DEFAULT bndrs rhs)
  = assert (null bndrs) $ do
    let (env', _) = setDef env caseBndr (NotAmong notAmong)
    rhs' <- simplCommandNoFloats env' rhs
    return $ Alt DEFAULT [] rhs'
simplAlt env scrut_maybe _ caseBndr (Alt (LitAlt lit) bndrs rhs)
  = assert (null bndrs) $ do
    env' <- addAltUnfoldings env scrut_maybe caseBndr (Lit lit)
    rhs' <- simplCommandNoFloats env' rhs
    return $ Alt (LitAlt lit) [] rhs'
simplAlt env scrut' _ case_bndr' (Alt (DataAlt con) vs rhs)
  = do  {       -- Deal with the pattern-bound variables
                -- Mark the ones that are in ! positions in the
                -- data constructor as certainly-evaluated.
                -- NB: simplLamBinders preserves this eval info
        ; let vs_with_evals = add_evals (dataConRepStrictness con)
        ; let (env', vs') = enterLamScopes env vs_with_evals

                -- Bind the case-binder to (con args)
        ; let inst_tys' = tyConAppArgs (idType case_bndr')
              con_app :: OutTerm
              con_app = mkConstruction con inst_tys' (map mkVarArg vs')

        ; env'' <- addAltUnfoldings env' scrut' case_bndr' con_app
        ; rhs' <- simplCommandNoFloats env'' rhs
        ; return $ Alt (DataAlt con) vs' rhs' }
  where
        -- add_evals records the evaluated-ness of the bound variables of
        -- a case pattern.  This is *important*.  Consider
        --      data T = T !Int !Int
        --
        --      case x of { T a b -> < T | $ (a+1); $ b; ret > }
        --
        -- We really must record that b is already evaluated so that we don't
        -- go and re-evaluate it when constructing the result.
        -- See Note [Data-con worker strictness] in MkId.lhs
    add_evals the_strs
        = go vs the_strs
        where
          go [] [] = []
          go (v:vs') strs | isTyVar v = v : go vs' strs
          go (v:vs') (str:strs)
            | isMarkedStrict str = evald_v  : go vs' strs
            | otherwise          = zapped_v : go vs' strs
            where
              zapped_v = zapIdOccInfo v   -- See Note [Case alternative occ info]
              evald_v  = zapped_v `setIdUnfolding` evaldUnfolding
          go _ _ = pprPanic "cat_evals" (ppr con $$ ppr vs $$ ppr the_strs)

addAltUnfoldings :: SimplEnv -> Maybe OutTerm -> OutId -> OutTerm -> SimplM SimplEnv
addAltUnfoldings env scrut case_bndr con_app
  = do { let con_app_def = mkDef env NotTopLevel (Left con_app)
             (env1, _) = setDef env case_bndr con_app_def

             -- See Note [Add unfolding for scrutinee]
             (env2, _) = case scrut of
                      Just (Var v)           -> setDef env1 v con_app_def
                      Just (Compute _ (Eval (Var v) (Kont [Cast co] Return)))
                                             -> setDef env1 v $
                                                mkDef env1 NotTopLevel (Left (mkCast con_app (mkSymCo co)))
                      _                      -> (env1, undefined)

       ; when tracing $ pprTraceShort "addAltUnf" (vcat [ppr case_bndr <+> ppr scrut, ppr con_app]) return ()
       ; return env2 }

simplVar :: SimplEnv -> InVar -> SimplM OutTerm
simplVar env x
  | isTyVar x = return $ Type (substTyVar env x)
  | isCoVar x = return $ Coercion (substCoVar env x)
  | otherwise
  = case substId env x of
    DoneId x' -> return $ Var x'
    Done v -> return v
    Susp stat v -> simplTermNoFloats (env `setStaticPart` stat) BoringCtxt v

simplJump :: SimplEnv -> [InArg] -> InPKontId -> SimplM (SimplEnv, OutCommand)
simplJump env args j
  | tracing
  , pprTraceShort "simplJump" (ppr env $$ parens (pprWithCommas ppr args) $$ ppr j)
    False
  = undefined
simplJump env args j
  = case substPv env j of
      DoneId j'
        -> do
           let lone = null args
               -- Pretend to callSiteInline that we're just applying a bunch of
               -- arguments to a function
               rhs'_maybe = callSiteInline env j' (activeUnfolding env j') lone 
                                           frames end
          
           case rhs'_maybe of
             Nothing
               -> simplKont env (mkJumpArgInfo env j' frames) frames end
                    -- Activate case 2 of simplKont (Note [simplKont invariants])
             Just (Right pk')
               -> do
                  tick (UnfoldingDone j')
                  reduce (zapSubstEnvs env) pk'
             _ -> pprPanic "simplJump" (ppr j $$ ppr rhs'_maybe)
      Done pk
        -> reduce (zapSubstEnvs env) pk
      Susp stat' pk
        -> reduce (env `setStaticPart` stat') pk
  where
    stat   = staticPart env
    frames = map (Incoming stat . App) args
    end    = Incoming stat Return
    reduce env_pk pk
      = simplKont env_pk (mkPKontArgInfo env_pk (Incoming (staticPart env_pk) pk) frames)
                  frames end

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
postInlineUnconditionally :: SimplEnv -> OutBindPair -> TopLevelFlag -> Definition
                          -> SimplM Bool
postInlineUnconditionally env pair level def
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
      | defIsStable def             = False
      | either isTrivialTerm isTrivialPKont rhs = True
      | otherwise
      = case occ_info of
          OneOcc in_lam _one_br int_cxt
            ->     defIsSmallEnoughToInline dflags def
               && (not in_lam ||
                    (defIsCheap def && int_cxt))
          IAmDead -> True
          _ -> False

      where
        (x, rhs) = destBindPair pair
        occ_info = idOccInfo x
        active = isActive (sm_phase mode) (idInlineActivation x)

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

callSiteInline :: SimplEnv -> OutId -> Bool -> Bool -> [ScopedFrame] -> ScopedEnd -> Maybe OutRhs
callSiteInline env id active_unfolding lone_variable fs end
  = case findDef env id of 
      -- idUnfolding checks for loop-breakers, returning NoUnfolding
      -- Things with an INLINE pragma may have an unfolding *and* 
      -- be a loop breaker  (maybe the knot is not yet untied)
      BoundTo { def_rhs = unf_template, def_level = is_top 
              , def_isWorkFree = is_wf,  def_arity = uf_arity
              , def_guidance = guidance, def_isExpandable = is_exp }
              | active_unfolding -> let (arg_infos, cont_info) = distillKont env fs end
                                    in tryUnfolding (dynFlags env) id lone_variable
                                        arg_infos cont_info unf_template (isTopLevel is_top)
                                        is_wf is_exp uf_arity guidance
              | let dflags = dynFlags env
              , tracing || dopt Opt_D_dump_inlinings dflags && dopt Opt_D_verbose_core2core dflags
              -> pprTrace "Inactive unfolding:" (ppr id) Nothing
              | otherwise -> Nothing
      _       -> Nothing

-- Impedence mismatch between Sequent Core code and logic from CoreUnfold.
distillKont :: SimplEnv -> [ScopedFrame] -> ScopedEnd -> ([ArgSummary], CallCtxt)
distillKont env fs end = (mapMaybe (doFrame . unScope) fs, doEnd (unScope end))
  where
    doFrame (App v)    | not (isTypeArg v)
                       = Just (interestingArg v)
    doFrame _          = Nothing
    
    doEnd (Return {})  = getContext env
    doEnd (Case {})    = CaseCtxt

tryUnfolding :: DynFlags -> Id -> Bool -> [ArgSummary] -> CallCtxt
             -> OutRhs -> Bool -> Bool -> Bool -> Arity -> Guidance
             -> Maybe OutRhs
tryUnfolding dflags id lone_variable 
             arg_infos cont_info unf_template is_top 
             is_wf is_exp uf_arity guidance
                        -- uf_arity will typically be equal to (idArity id), 
                        -- but may be less for InlineRules
 | tracing || dopt Opt_D_dump_inlinings dflags && dopt Opt_D_verbose_core2core dflags
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
  | Just mk <- substKv env
  , not (canDupMetaKont mk)
  = do
    (env', mk') <- mkDupableKont (zapFloats env) (retType env) mk
    return $ (env `addFloats` env') `setRetKont` mk'
  | otherwise
  = return env

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
      SynKont { mk_frames = fs, mk_end = end }
        -> do
           (env', fs', end') <- go env_noFloats [] ty fs end
           return (env', SynKont { mk_dup = OkToDup
                                 , mk_frames = map (Simplified OkToDup Nothing) fs'
                                 , mk_end = end' })
      StrictArg { mk_argInfo = ai
                , mk_frames  = fs
                , mk_end     = end }
        -> do
           (env', fs', end') <- go env_noFloats [] ty fs end
           (env'', ai') <- case ai_dup ai of
             NoDup -> do 
                      (env'', outFrames) <- mapAccumLM (makeTrivialFrame NotTopLevel) env' (ai_frames ai)
                      return (env'', ai { ai_frames = outFrames, ai_dup = OkToDup })
             OkToDup -> return (env', ai)
           return (env'', kont { mk_dup     = OkToDup
                               , mk_argInfo = ai'
                               , mk_frames  = map (Simplified OkToDup Nothing) fs'
                               , mk_end     = end' })
      _ -> do
           (env', joinKont) <- mkJoinPoint env ty (fsLit "*mkj") kont
           return (env', SynKont { mk_dup = OkToDup
                                 , mk_frames = []
                                 , mk_end = Simplified OkToDup Nothing joinKont })
           
    when tracing $ liftCoreM $ putMsg $ hang (text "mkDupableKont DONE") 4 $
      ppr ans $$ vcat (map ppr (getFloatBinds (getFloats env')))
    return (env `addFloats` env', ans)
  where
    go :: SimplEnv -> RevList OutFrame -> OutType
       -> [ScopedFrame] -> ScopedEnd
       -> SimplM (SimplEnv, [OutFrame], ScopedEnd)
    go env fs' ty (f : fs) end
      | Simplified OkToDup _ f' <- f
      = go env (f' : fs') (frameType ty f') fs end
      | otherwise
      = case openScoped env f of
          (env', f') -> doFrame env' fs' ty f' f fs end
    go env fs' ty [] end
      = case openScoped env end of
          (env', end') -> doEnd env' fs' ty end' end
    
    doFrame :: SimplEnv -> RevList OutFrame -> OutType
            -> InFrame -> ScopedFrame -> [ScopedFrame] -> ScopedEnd
            -> SimplM (SimplEnv, [OutFrame], ScopedEnd)
    doFrame env fs' _ty (Cast co) _ fs end
      = let co' = simplCoercion env co
        in go env (Cast co' : fs') (pSnd (coercionKind co')) fs end
    
    doFrame env fs' ty (Tick {}) f_orig fs end
      = split env fs' ty (f_orig : fs) end (fsLit "*tickj")
    
    doFrame env fs' ty (App (Type tyArg)) _ fs end
      = let tyArg' = substTy env tyArg
            ty'    = applyTy ty  tyArg'
        in go env (App (Type tyArg') : fs') ty' fs end
    
    doFrame env fs' ty (App arg) _ fs end
      = do
        (env', arg') <- mkDupableTerm env arg
        go env' (App arg' : fs') (funResultTy ty) fs end

    doEnd :: SimplEnv -> RevList OutFrame -> OutType
          -> InEnd -> ScopedEnd
          -> SimplM (SimplEnv, [OutFrame], ScopedEnd)
    doEnd env fs' ty Return _
      = case substKv env of
          Nothing                -> done env fs' (Simplified OkToDup Nothing Return)
          Just mk                 | canDupMetaKont mk
                                 -> done env fs' (Simplified OkToDup (Just mk) Return)
          Just (SynKont { mk_frames = fs, mk_end = end })
                                 -> go env fs' ty fs end
          Just (mk@StrictArg { mk_argInfo = ai })
                                 -> do
                                    let ty'  = funResultTy (termType (argInfoToTerm ai))
                                    (env', mk') <- mkDupableKont env ty' mk
                                    done env' fs' (Simplified OkToDup (Just mk') Return)
          Just mk                -> split env fs' ty [] (Simplified OkToDup (Just mk) Return)
                                                        (fsLit "*imkj")
    
    -- Don't duplicate seq (see Note [Single-alternative cases] in GHC Simplify.lhs)
    doEnd env fs' ty (Case caseBndr [Alt _altCon bndrs _rhs]) end_orig
      | all isDeadBinder bndrs
      , not (isUnLiftedType (idType caseBndr))
      = split env fs' ty [] end_orig (fsLit "*seqj")

    doEnd env fs' _ty (Case caseBndr alts) _
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
        
        done env' fs' (Simplified OkToDup Nothing (Case caseBndr' alts''))

    split :: SimplEnv -> RevList OutFrame -> Type -> [ScopedFrame] -> ScopedEnd
          -> FastString
          -> SimplM (SimplEnv, [OutFrame], ScopedEnd)
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
        (env_final, join_kont)
          <- mkJoinPoint env ty name (SynKont { mk_frames = fs
                                              , mk_end    = end
                                              , mk_dup    = NoDup })
        done env_final fs' (Simplified OkToDup Nothing join_kont)
    
    done :: SimplEnv -> RevList OutFrame -> ScopedEnd
         -> SimplM (SimplEnv, [OutFrame], ScopedEnd)
    done env fs end = return (env, reverse fs, end)
    
    mkJoinPoint env ty name mk
      = do
        let kontTy = mkKontTy (mkTupleTy UnboxedTuple [ty])
        (env', j) <- mkFreshVar env name kontTy
        let (env'', x) = enterScope env' (mkKontArgId ty)
            env_rhs   = env'' `setRetKont` mk
            join_rhs  = PKont [x] (Eval (Var x) (Kont [] Return))
            join_kont = Case x [Alt DEFAULT [] (Jump [Var x] j)]
        env_final <- simplPKontBind env'' j j (staticPart env_rhs) join_rhs NonRecursive
        return (env_final, join_kont)
    
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

