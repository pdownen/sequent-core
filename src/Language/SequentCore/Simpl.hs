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
import CoreSubst   ( deShadowBinds )
import CoreSyn     ( CoreVect(..), isRuntimeVar, isCheapUnfolding, isConLikeUnfolding )
import CoreUnfold  ( smallEnoughToInline )
import DynFlags    ( DynFlags, gopt, GeneralFlag(..), ufKeenessFactor, ufUseThreshold )
import FastString
import Id
import IdInfo      ( IdInfo, demandInfo, strictnessInfo, vanillaIdInfo,
                     setArityInfo, setDemandInfo, setStrictnessInfo )
import HscTypes    ( ModGuts(..), VectInfo(..) )
import Literal     ( litIsDupable )
import Maybes      ( whenIsJust )
import MonadUtils
import Name        ( mkSystemVarName )
import Outputable
import Pair
import qualified PprCore as Core
import Type        ( Type, applyTy, funResultTy, isUnLiftedType, mkTyVarTy )
import TysWiredIn  ( mkTupleTy )
import UniqSupply
import Var
import VarEnv
import VarSet

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
    = CoreDoPluginPass "SeqSimpl" (runSimplifier (3*max) mode) -- TODO Use less gas

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
    when linting $ whenIsJust (lintCoreBindings binds) $ \err ->
      pprPgmError "Sequent Core Lint error (pre-simpl)"
        (withPprStyle defaultUserStyle $ err
                                      $$ pprTopLevelBinds binds 
                                      $$ text "--- Original Core: ---"
                                      $$ Core.pprCoreBindings coreBinds)
    binds' <- go 1 binds
    let coreBinds' = bindsToCore binds'
    when dumping $ putMsg  $ text "FINAL CORE"
                          $$ text "----------"
                          $$ Core.pprCoreBindings coreBinds'
    return $ guts { mg_binds = coreBinds' }
  where
    rules = mg_rules guts

    go n binds
      | n > iters
      = do
        errorMsg  $  text "Ran out of gas after"
                 <+> int iters
                 <+> text "iterations."
        return binds
      | otherwise
      = do
        dflags <- getDynFlags
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
            env = initialEnv dflags mode
            occBinds = runOccurAnal env mod maybeVects maybeVectVars binds
        when dumping $ putMsg  $ text "BEFORE" <+> int n
                              $$ text "--------" $$ pprTopLevelBinds occBinds
        when linting $ whenIsJust (lintCoreBindings occBinds) $ \err ->
          pprPanic "Sequent Core Lint error (in occurrence analysis)"
            (withPprStyle defaultUserStyle $ err)
        (binds', count) <- runSimplM $ simplModule env occBinds
        when linting $ whenIsJust (lintCoreBindings binds') $ \err ->
          pprPanic "Sequent Core Lint error"
            (withPprStyle defaultUserStyle $ err $$ pprTopLevelBinds binds')
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
    runOccurAnal env mod vects vectVars binds
      = let isRuleActive = activeRule env
        in occurAnalysePgm mod isRuleActive rules vects vectVars binds

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
  = simplCut env term (staticPart env) fs end
simplCommand env (Jump args j)
  = simplJump env args j

simplTermNoFloats :: SimplEnv -> InTerm -> SimplM OutTerm
simplTermNoFloats env (Compute p comm)
  = do
    let (env', p') = enterScope env p
    comm' <- simplCommandNoFloats env' comm
    return $ mkCompute p' comm'
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
    (env''', comm) <- simplCut env'' v (staticPart env'') [] (Return p)
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
        (env_v_final, v'') <- prepareRhsTerm env_v'' level x' v'
        (env_x', v''')
          <- if not (doFloatFromRhs level recFlag False v'' env_v_final)
                then do v''' <- wrapFloatsAroundTerm env_v_final v''
                        return (env_x, v''')
                else do tick LetFloatFromLet
                        return (env_x `addFloats` env_v_final, v'')
        completeBind env_x' x x' (Left v''') level

prepareRhsTerm :: SimplEnv -> TopLevelFlag -> OutId -> OutTerm
               -> SimplM (SimplEnv, OutTerm)
prepareRhsTerm env _ _ v
  | isTrivialTerm v
  = return (env, v)
prepareRhsTerm env level x (Compute p comm)
  = do
    (env', term') <- prepComm env comm
    return (env', term')
  where
    prepComm env (Eval term (Kont fs (Return p')))
      = assert (p == p') $ do
        (_isExp, env', fs', co_maybe) <- go (0 :: Int) fs
        case co_maybe of
          Just co -> do
                     let Pair fromTy _toTy = coercionKind co
                     -- Don't use mkFreshKontId here because it sets the current continuation
                     (env'', q) <- mkFreshVar env' (fsLit "*castk") (mkKontTy fromTy)
                     (env''', x') <- mkFreshVar env'' (fsLit "ca") (kontTyArg (idType q))
                     -- x' shares its strictness and demand info with x, since
                     -- x only adds a cast to x'
                     let info = idInfo x
                         sanitizedInfo = vanillaIdInfo `setStrictnessInfo` strictnessInfo info
                                                       `setDemandInfo` demandInfo info
                         x'_final = x' `setIdInfo` sanitizedInfo
                         x'_rhs = Compute q (Eval term (Kont fs' (Return q)))
                     if isTrivialTerm x'_rhs
                       then -- No sense turning one trivial term into two, as
                            -- the simplifier will just end up substituting one
                            -- into the other and keep on looping
                            return (env', Compute p (Eval term (Kont fs' (Return p))))
                       else do
                            env'''' <- completeNonRecTerm env''' False x'_final x'_final x'_rhs level
                            x'_final_value <- simplVar env'''' x'_final
                            return (env'''', Compute p (Eval x'_final_value (Kont [Cast co] (Return p))))
          Nothing -> return (env', Compute p (Eval term (Kont fs' (Return p))))
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
        --   * A function representing the new continuation, but perhaps without
        --     the Return (in the sense that a difference list is a list without
        --     its end). This is represented as the ellipses above. If we do a
        --     coercion split, this will end up in the new binding; otherwise,
        --     it will stay in the original one.
        --   * The top-level coercion, if we're doing a coercion split.
        -- 
        -- TODO It would be easier to pass everything downward instead,
        -- employing a bit of knot-tying for the Bool, but for some reason
        -- there's no MonadFix CoreM, so we can't write MonadFix SimplM.
        go :: Int -> [OutFrame] -> SimplM (Bool, SimplEnv, [OutFrame], Maybe Coercion)
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
      = return (env, Compute p comm)
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
        let rhs = mkSuspension env_pk pk
            env' = extendPvSubst env_j j rhs
        return env'
      else do
        (env_j', xs', comm') <-
          case pk of
            PKont [] comm -> do
              -- No parameters, so we can float things out
              let env_pk' = zapFloats (env_pk `inDynamicScope` env_j)
              (env_with_floats, comm') <- simplCommand env_pk' comm
              -- TODO Something like Simplify.prepareRhs
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
-- simplLazyBind and simplPKontBind, here we *have* to substitute (that is,
-- either pre-inline or post-inline) since we can't give a continuation a
-- let binding.
simplKontBind :: SimplEnv -> InKontId -> StaticEnv -> InKont -> SimplM SimplEnv
simplKontBind env_p p env_k k
  | tracing
  , pprTraceShort "simplKontBind" (pprBndr LetBind p $$ ppr k) False
  = undefined
  | preInline
  = do
    tick $ PreInlineUnconditionally p
    return env_p' { se_retKont = Just (Susp env_k k) }
  | otherwise
  = do
    tick $ PostInlineUnconditionally p
    (env_k', k') <- mkDupableKont (zapFloats (env_k `inDynamicScope` env_p'))
                                  (kontTyArg (substTy env_p (idType p)))
                                  k
    return (env_p' `addFloats` env_k') { se_retKont = Just (Done k') }
  where
    (env_p', _) = enterScope env_p p -- ignore cloned p because we're
                                     -- substituting anyway
    
    -- Pre-inline (i.e. substitute whole rather than making it dupable first)
    -- whenever 
    preInline
      = case idOccInfo p of
          OneOcc _ notInBranch _ -> notInBranch
          other                  -> warnPprTrace True __FILE__ __LINE__
                                    (text "weird OccInfo for cont var"
                                      <+> ppr p <> colon <+> ppr other)
                                    False

{-
Note [Wrap around compute]
~~~~~~~~~~~~~~~~~~~~~~~~~~

Suppose we have floats F and we wrap around a term (compute p. c), that is, we
calculate

F[compute p. c].

Remembering that terms are continuation-closed, we know two things:

1. Any continuations let-bound in F will be dead bindings, and
2. Any terms bound in F can float into c.

We are safe, then, in saying

F[compute p. c] = compute p. F'[c],

where F' contains only the term bindings from F. Of course, if a binding *is*
trying to float up past a compute, something has gone very wrong, so we check
for this condition and warn.
-}

wrapFloatsAroundTerm :: SimplEnv -> OutTerm -> SimplM OutTerm
wrapFloatsAroundTerm env term
  | isEmptyFloats env
  = return term
wrapFloatsAroundTerm env (Compute p comm)
  -- See Note [Wrap around compute]
  = warnPprTrace (not $ hasNoKontFloats env) __FILE__ __LINE__
      (text "cont floats escaping body of command:" <+> ppr comm $$
       text "floats:" <+> brackets (pprWithCommas (ppr . bindersOf)
                                                  (getFloatBinds (getFloats env)))) $
    return $ Compute p (wrapFloats (zapKontFloats env) comm)
wrapFloatsAroundTerm env term
  = do
    let ty = termType term
    (env', k) <- mkFreshKontId env (fsLit "*wrap") ty
    return $ mkCompute k $ wrapFloats env' (mkCommand [] term (Kont [] (Return k)))

completeNonRecTerm :: SimplEnv -> Bool -> InVar -> OutVar -> OutTerm
               -> TopLevelFlag -> SimplM SimplEnv
completeNonRecTerm env is_strict old_bndr new_bndr new_rhs top_lvl
 = do  { (env1, rhs1) <- prepareRhsTerm (zapFloats env) top_lvl new_bndr new_rhs
       ; (env2, rhs2) <-
               if doFloatFromRhs NotTopLevel NonRecursive is_strict rhs1 env1
               then do { tick LetFloatFromLet
                       ; return (addFloats env env1, rhs1) }     -- Add the floats to the main env
               else do { rhs1' <- wrapFloatsAroundTerm env1 rhs1 -- Wrap the floats around the RHS
                       ; return (env, rhs1') }
       ; completeBind env2 old_bndr new_bndr (Left rhs2) NotTopLevel }

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

mkDef :: SimplEnv -> TopLevelFlag -> OutRhs -> SimplM Definition
mkDef env level rhs
  = do
    dflags <- getDynFlags
    -- FIXME Make a BoundToDFun when possible
    return $ case rhs of
               Left term -> mkBoundTo env dflags term (termArity term) level
               Right pkont -> mkBoundToPKont dflags pkont

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

-- TODO Deal with casts. Should maybe take the active cast as an argument;
-- indeed, it would make sense to think of a cut as involving a term, a
-- continuation, *and* the coercion that proves they're compatible.
simplCut :: SimplEnv -> InTerm -> StaticEnv -> [InFrame] -> InEnd
                     -> SimplM (SimplEnv, OutCommand)
simplCut env_v v env_k fs end
  | tracing
  , pprTraceShort "simplCut" (
      ppr env_v $$ ppr v $$ ppr env_k $$ ppr (Kont fs end)
    ) False
  = undefined
simplCut env_v v env_k [] (Return p)
  = case substKv (env_k `inDynamicScope` env_v) p of
      DoneId p'      -> simplCut2 (p /= p') env_v v env_k [] (Return p')
      Done k'        -> simplCut2 True  env_v v (zapSubstEnvsStatic env_k) fs' end'
        where Kont fs' end' = k'
      Susp env_k' k' -> simplCut        env_v v env_k' fs' end'
        where Kont fs' end' = k'
simplCut env_v v env_k fs end
  = simplCut2 False env_v v env_k fs end

-- Second phase of simplCut. Now, if the continuation is a variable, it has no
-- substitution (it's a parameter). In other words, if it's a KontId, it's an
-- OutKontId.
simplCut2 :: Bool -> SimplEnv -> InTerm -> StaticEnv -> [InFrame] -> InEnd
          -> SimplM (SimplEnv, OutCommand)
simplCut2 verb env_v v env_k fs end
  | tracing, verb
  , pprTraceShort "simplCut2" (
      ppr env_v $$ ppr v $$ ppr env_k $$ ppr (Kont fs end)
    ) False
  = undefined
simplCut2 _ env_v (Var x) env_k fs end
  = case substId env_v x of
      DoneId x'
        -> do
           let lone | App {} : _ <- fs = False
                    | otherwise        = True
           let term'_maybe = callSiteInline env_v x' (activeUnfolding env_v x')
                                            lone (Kont fs end)
           case term'_maybe of
             Nothing
               -> simplCut3 (x /= x') env_v (Var x') env_k fs end
             Just term'
               -> do
                  tick (UnfoldingDone x')
                  simplCut2 True (zapSubstEnvs env_v) term' env_k fs end
      Done v
        -- Term already simplified (then PostInlineUnconditionally'd), so
        -- don't do any substitutions when processing it again
        -> simplCut3 True (zapSubstEnvs env_v) v env_k fs end
      Susp stat v
        -> simplCut2 True (env_v `setStaticPart` stat) v env_k fs end
simplCut2 _ env_v term env_k fs end
  -- Proceed to phase 3
  = simplCut3 False env_v term env_k fs end

-- Third phase of simplCut. Now, if the term is a variable, we looked it up
-- and substituted it but decided not to inline it. (In other words, if it's an
-- id, it's an OutId.)
simplCut3 :: Bool -> SimplEnv -> OutTerm -> StaticEnv -> [InFrame] -> InEnd
          -> SimplM (SimplEnv, OutCommand)
simplCut3 verb env_v v env_k fs end
  | tracing, verb
  , pprTraceShort "simplCut3" (
      ppr env_v $$ ppr v $$ ppr env_k $$ ppr (Kont fs end)
    ) False
  = undefined
simplCut3 _ env_v (Type ty) _env_k fs end
  = assert (null fs && isReturn end) $
    let ty' = substTy env_v ty
    in return (env_v, Eval (Type ty') (Kont fs end))
simplCut3 _ env_v (Coercion co) _env_k fs end
  = assert (null fs && isReturn end) $
    let co' = substCo env_v co
    in return (env_v, Eval (Coercion co') (Kont fs end))
simplCut3 _ env_v (Lam x body) env_k (App arg : fs) end
  = do
    tick (BetaReduction x)
    env_v' <- simplNonRec env_v x env_k arg NotTopLevel
    simplCut env_v' body env_k fs end
simplCut3 _ env_v term@(Lam {}) env_k fs end
  = do
    let (xs, body) = lambdas term
        (env_v', xs') = enterScopes env_v xs
    body' <- simplTermNoFloats env_v' body
    simplKontWith (env_v' `setStaticPart` env_k) (mkLambdas xs' body') fs end
simplCut3 _ env_v term env_k fs end
  | Just (value, Kont [] (Case x alts)) <- splitValue term (Kont fs end)
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
simplCut3 _ env_v term env_k [] (Case case_bndr [Alt _ bndrs rhs])
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

simplCut3 _ env_v (Compute p c) env_k fs end
  = do
    env_v' <- simplKontBind env_v p env_k (Kont fs end)
    simplCommand env_v' c
simplCut3 _ env_v term@(Lit {}) env_k fs end
  = simplKontWith (env_v `setStaticPart` env_k) term fs end
simplCut3 _ env_v term@(Var {}) env_k fs end
  = simplKontWith (env_v `setStaticPart` env_k) term fs end

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

simplKont :: SimplEnv -> [InFrame] -> InEnd -> SimplM (SimplEnv, OutKont)
simplKont env fs end
  | tracing
  , pprTraceShort "simplKont" (
      ppr env $$ ppr (Kont fs end)
    ) False
  = undefined
simplKont env fs end
  = go env fs end []
  where
    go :: SimplEnv -> [InFrame] -> InEnd -> [OutFrame] -> SimplM (SimplEnv, OutKont)
    go env fs end _
      | tracing
      , pprTraceShort "simplKont::go" (
          ppr env $$ ppr (Kont fs end)
        ) False
      = undefined
    go env (App arg : fs) end fs'
      -- TODO Handle strict arguments differently? GHC detects whether arg is
      -- strict, but here we've lost that information.
      = do
        -- Don't float out of arguments (see Simplify.rebuildCall)
        arg' <- simplTermNoFloats env arg
        go env fs end (App arg' : fs')
    go env (Cast co : fs) end fs'
      = do
        co' <- simplCoercion env co
        go env fs end (Cast co' : fs')
    go env [] (Case x alts) fs'
      = do
        let (env', x') = enterScope env x
        -- FIXME The Nothing there could be the scrutinee, but we don't ever
        -- have access to it here.
        alts' <- forM alts (simplAlt env' Nothing [] x')
        done env fs' (Case x' alts')
    go env (Tick ti : fs) end fs'
      = go env fs end (Tick ti : fs')
    go env [] (Return x) fs'
      = case substKv env x of
          DoneId x'
            -> done env fs' (Return x')
          Done (Kont fs end)
            -> go (zapSubstEnvs env) fs end fs'
          Susp stat (Kont fs end)
            -> go (env `setStaticPart` stat) fs end fs'
    
    done env' fs' end'
      = return (env', Kont (reverse fs') end')

simplKontWith :: SimplEnv -> OutTerm -> [InFrame] -> InEnd
              -> SimplM (SimplEnv, OutCommand)
simplKontWith env term fs end
  = do
    (env', kont') <- simplKont env fs end
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

data ArgSummary = TrivArg        -- Nothing interesting
                | NonTrivArg        -- Arg has structure
                | ValueArg        -- Arg is a con-app or PAP
                            -- ..or con-like. Note [Conlike is interesting]

interestingArg :: SeqCoreTerm -> ArgSummary
-- See Note [Interesting arguments]
interestingArg e = goT e 0
  where
    -- n is # value args to which the expression is applied
    goT (Lit {}) _              = ValueArg
    goT (Var v)  n
       | isConLikeId v     = ValueArg        -- Experimenting with 'conlike' rather that
                                             --    data constructors here
       | idArity v > n           = ValueArg  -- Catches (eg) primops with arity but no unfolding
       | n > 0                   = NonTrivArg        -- Saturated or unknown call
       | conlike_unfolding = ValueArg        -- n==0; look for an interesting unfolding
                                      -- See Note [Conlike is interesting]
       | otherwise         = TrivArg        -- n==0, no useful unfolding
       where
         conlike_unfolding = isConLikeUnfolding (idUnfolding v)

    goT (Type _)         _ = TrivArg
    goT (Coercion _)     _ = TrivArg
    goT (Lam v e)           n 
       | isTyVar v     = goT e n
       | n>0           = goT e (n-1)
       | otherwise     = ValueArg
    goT (Compute _ c) n    = goC c n
    
    goC (Let _ c)    n = case goC c n of { ValueArg -> ValueArg; _ -> NonTrivArg }
    goC (Eval v k)   n = maybe NonTrivArg (goT v) (goK k n)
    goC (Jump vs j)  _ = goT (Var j) (length (filter isValueArg vs))
    
    goK (Kont _ (Case {}))   _ = Nothing
    goK (Kont fs (Return _)) n = Just $ length (filter realArg fs) + n
    
    realArg (App (Type _))     = False
    realArg (App (Coercion _)) = False
    realArg (App _)            = True
    realArg _                  = False

nonTriv ::  ArgSummary -> Bool
nonTriv TrivArg = False
nonTriv _       = True


instance Outputable ArgSummary where
  ppr TrivArg    = ptext (sLit "TrivArg")
  ppr NonTrivArg = ptext (sLit "NonTrivArg")
  ppr ValueArg   = ptext (sLit "ValueArg")

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
      Just BoundTo { defTerm = unf_template, defLevel = is_top 
                 , defIsWorkFree = is_wf, defArity = uf_arity
                   , defGuidance = guidance, defIsExpandable = is_exp }
                   | active_unfolding -> let (arg_infos, cont_info) = distillKont kont
                                         in tryUnfolding (se_dflags env) id lone_variable
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
--   5. Duplicate cases, but "ANF-ize" in a dual sense by creating a join point
--        for each branch.

mkDupableKont :: SimplEnv -> Type -> InKont -> SimplM (SimplEnv, OutKont)
mkDupableKont env ty kont
  = do
    when tracing $ liftCoreM $ putMsg $ hang (text "mkDupableKont") 4 (ppr env $$ ppr ty $$ ppr kont)
    let Kont fs end = kont
    (env', ans) <- go env [] ty fs end
    when tracing $ liftCoreM $ putMsg $ hang (text "mkDupableKont DONE") 4 $
      ppr ans $$ vcat (map ppr (getFloatBinds (getFloats env')))
    return (env', ans)
  where
    -- The OutKont -> OutKont is a continuation for the outer continuation (!!).
    go :: SimplEnv -> [OutFrame] -> Type -> [InFrame] -> InEnd
       -> SimplM (SimplEnv, OutKont)
    go env fs' ty [] (Return kid)
      = case substKv env kid of
          DoneId kid'               -> done env fs' (Return kid')
          Done (Kont fs end)        -> do
                                       let env' = zapSubstEnvs env
                                       go env' fs' ty fs end
          Susp stat (Kont fs end)   -> do
                                       let env' = stat `inDynamicScope` env
                                       go env' fs' ty fs end
    
    go env fs' _ty (Cast co : fs) end
      = do
        co' <- simplCoercion env co
        go env (Cast co' : fs') (pSnd (coercionKind co')) fs end
    
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
        
        done env' fs' (Case caseBndr' alts'')
        
    split :: SimplEnv -> [OutFrame] -> Type -> [InFrame] -> InEnd -> FastString
          -> SimplM (SimplEnv, OutKont)
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
        let kontTy = mkKontTy (mkKontArgsTy (mkTupleTy UnboxedTuple [ty]))
        (env', j) <- mkFreshVar env name kontTy
        let (env'', x) = enterScope env' (mkKontArgId ty)
            join_rhs  = PKont [x] (Eval (Var x) (Kont fs end))
            join_kont = Case x [Alt DEFAULT [] (Jump [Var x] j)]
        env_final <- simplPKontBind env'' j j (staticPart env'') join_rhs NonRecursive
        
        done env_final fs' join_kont
    
    done :: SimplEnv -> [OutFrame] -> OutEnd -> SimplM (SimplEnv, OutKont)
    done env fs end = return (env, Kont (reverse fs) end)
    
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
    
    go n (K (Kont fs (Return _))) = goF n fs
    
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
        ; env'  <- completeNonRecTerm env False var var term top_lvl
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

