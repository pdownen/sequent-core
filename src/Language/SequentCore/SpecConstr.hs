-- |
-- Module      : Language.SequentCore.SpecConstr
-- Description : SpecConstr reimplementation
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- A simple reimplementation of the SpecConstr pass using Sequent Core.
--
-- Based on
-- <http://research.microsoft.com/en-us/um/people/simonpj/papers/spec-constr Call-pattern specialization for Haskell programs>,
-- Simon Peyton Jones, submitted to ICFP 2007. 

module Language.SequentCore.SpecConstr (
  plugin
) where

import Language.SequentCore.Ops
import Language.SequentCore.Plugin
import Language.SequentCore.Pretty ()
import Language.SequentCore.Syntax

import CoreMonad  ( CoreM
                  , Plugin(installCoreToDos), defaultPlugin
                  , errorMsg
                  , reinitializeGlobals
                  , CoreToDo(CoreDoSpecConstr, CoreDoPasses, CoreDoPluginPass) )
import CoreUnfold ( couldBeSmallEnoughToInline )
import CoreSyn    ( CoreRule )
import DynFlags   ( DynFlags(specConstrThreshold), getDynFlags )
import FastString ( fsLit, mkFastString )
import Id         ( Id, mkSysLocalM, idName, idInlineActivation )
import Name       ( nameOccName, occNameString )
import Outputable
import Rules      ( mkRule, addIdSpecialisations )
import Var        ( Var, varType )
import VarEnv
import VarSet

import Control.Applicative  ( (<$>), (<|>) )
import Control.Monad
import Data.List            ( nubBy )
import Data.Monoid

-- | Plugin data. The initialization code replaces the built-in SpecConstr pass
-- in the Core-to-Core pipeline.
plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = \_ todos -> do
    reinitializeGlobals
    case replace todos of
      Nothing ->
        do
          errorMsg (text "Could not find SpecConstr pass to replace")
          return todos
      Just todos' ->
        return todos'
} where
  replace (CoreDoSpecConstr : todos)
    = Just (specConstrPass : todos)
  replace (cdp@(CoreDoPasses todos1) : todos2)
    = do
        todos1' <- replace todos1
        return $ CoreDoPasses todos1' : todos2
      <|>
      do
        todos2' <- replace todos2
        return $ cdp : todos2'
  replace (todo : todos)
    = (todo :) <$> replace todos
  replace []
    = Nothing

  specConstrPass = CoreDoPluginPass "SeqSpecConstr" (sequentPass specModule)

data ScEnv
  = SCE { sc_size       :: Maybe Int
        , sc_how_bound  :: VarEnv HowBound
        , sc_dflags     :: DynFlags
        }

instance Outputable ScEnv where
  ppr (SCE { sc_size = sz, sc_how_bound = hb })
    = sep [hang (text "SCE {") 2 $ sep [
        text "sc_size" <+> equals <+> maybe (text "(any)") int sz <+> comma,
        text "sc_how_bound" <+> equals <+> ppr hb
      ], char '}']

data ScUsage = ScUsage Calls ArgUsage

instance Outputable ScUsage where
  ppr (ScUsage calls usage)
    = hang (text "ScUsage") 2 $ sep [ppr calls, ppr usage]

type Calls = VarEnv [Call]
type Call = [SeqCoreCommand]

data HowBound = SpecFun | SpecArg

instance Outputable HowBound where
  ppr SpecFun = text "SpecFun"
  ppr SpecArg = text "SpecArg"

type ArgUsage = VarSet

specModule :: [SeqCoreBind] -> CoreM [SeqCoreBind]
specModule binds = do
  env <- initScEnv <$> getDynFlags
  map snd <$> mapM (specInBind env) binds

initScEnv :: DynFlags -> ScEnv
initScEnv dflags = SCE { sc_size = specConstrThreshold dflags
                       , sc_how_bound = emptyVarEnv
                       , sc_dflags = dflags }

emptyScUsage :: ScUsage
emptyScUsage = ScUsage emptyVarEnv emptyVarSet

instance Monoid ScUsage where
  mempty
    = emptyScUsage
  ScUsage calls1 used1 `mappend` ScUsage calls2 used2
    = ScUsage (plusVarEnv_C (++) calls1 calls2) (used1 `unionVarSet` used2)

specInValue :: ScEnv -> SeqCoreValue -> CoreM (ScUsage, SeqCoreValue)
specInValue env (Lam x c)
  = do
    (usage, c') <- specInCommand env' c
    return (usage, Lam x c')
  where
    env' = env { sc_how_bound = extendVarEnv hb x SpecArg }
    hb   = sc_how_bound env 
specInValue _ v
  = return (emptyScUsage, v)

specInFrame :: ScEnv -> SeqCoreFrame -> CoreM (ScUsage, SeqCoreFrame)
specInFrame env (App c)
  = do
    (usage, c') <- specInCommand env c
    return (usage, App c')
specInFrame env (Case x t as)
  = do
    (usages, as') <- unzip <$> mapM (specInAlt env) as
    return (mconcat usages, Case x t as')
specInFrame _ f
  = return (emptyScUsage, f)

specInAlt :: ScEnv -> SeqCoreAlt -> CoreM (ScUsage, SeqCoreAlt)
specInAlt env (Alt ac xs c)
  = do
    (usage, c') <- specInCommand env c
    return (usage, Alt ac xs c')

specInBind :: ScEnv -> SeqCoreBind -> CoreM (ScUsage, SeqCoreBind)
specInBind env b
  = do
    (u, _, b') <- specBind env b
    return (u, b')

specInCommand :: ScEnv -> SeqCoreCommand -> CoreM (ScUsage, SeqCoreCommand)
specInCommand env (Command { cmdLet = bs, cmdValue = v, cmdCont = fs })
  = specBinds env bs [] []
  where
    specBinds :: ScEnv -> [SeqCoreBind] -> [SeqCoreBind] -> [ScUsage]
                       -> CoreM (ScUsage, SeqCoreCommand)
    specBinds env [] bs' usages
      = do
        (usage', v', fs') <- specInCut env v fs
        return (mconcat (usage' : usages), Command 
          { cmdLet = reverse bs', cmdValue = v', cmdCont = fs' })
    specBinds env (b : bs) bs' usages
      = do
        (usage', env', b') <- specBind env b
        specBinds env' bs (b' : bs') (usage' : usages)
    
specInCut :: ScEnv -> SeqCoreValue -> SeqCoreCont
        -> CoreM (ScUsage, SeqCoreValue, SeqCoreCont)
specInCut env v fs
  = do
    let u = usageFromCut env v fs
    (u_v, v') <- specInValue env v
    (us_fs, fs') <- unzip <$> mapM (specInFrame env) fs
    return (u `mappend` u_v `mappend` mconcat us_fs, v', fs')

usageFromCut :: ScEnv -> SeqCoreValue -> SeqCoreCont -> ScUsage
usageFromCut env (Var x) (Case {} : _)
  | Just SpecArg <- sc_how_bound env `lookupVarEnv` x
  = ScUsage emptyVarEnv (unitVarSet x)
usageFromCut env v@(Var f) fs
  | Just SpecFun <- sc_how_bound env `lookupVarEnv` f
  , Just (_, args, _) <- saturatedCall (Command [] v fs)
  = ScUsage (unitVarEnv f [args]) emptyVarSet
usageFromCut _ _ _
  = emptyScUsage

specBind :: ScEnv -> SeqCoreBind -> CoreM (ScUsage, ScEnv, SeqCoreBind)
specBind env (NonRec x c)
  = do
    (u, c') <- specInCommand env c
    return (u, env, NonRec x c')
specBind env (Rec bs)
  = do
    (usages, cs') <- unzip `liftM` mapM (specInCommand env' . snd) bs
    let
      totalUsages = mconcat usages
      bs'         = zip (map fst bs) cs'
    bindss <- mapM (specialize env' totalUsages) bs'
    return (totalUsages, env', Rec (concat bindss))
  where 
    env'  = env { sc_how_bound = hb' }
    hb'   = mkVarEnv [(x, SpecFun) | (x, _) <- bs] `plusVarEnv`
                    sc_how_bound env

data CallPat = [Var] :-> [SeqCoreCommand]

instance Outputable CallPat where
  ppr (xs :-> args) = ppr xs <+> text ":->" <+> ppr args

-- | A generated specialization---the call pattern that gave rise to it, the
-- identifier of the specialized function, and the function's definition.
data Spec = Spec {
  spec_pat :: CallPat,
  spec_id :: Id,
  spec_defn :: SeqCoreCommand
}

instance Outputable Spec where
  ppr spec
    = sep
      [ text "specialization for" <+> parens (ppr $ spec_pat spec)
      , text "id" <+> (ppr $ spec_id spec)
      , text "defn" <+> (ppr $ spec_defn spec)
      ]

specToBinding :: Spec -> (Var, SeqCoreCommand)
specToBinding (Spec { spec_id = x, spec_defn = c }) = (x, c)

-- | The kernel of the SpecConstr pass. Takes the environment, data about how
-- variables are used, and a let binding (part of a recursive block), and
-- returns a new list of bindings---the original one (with specialization rules
-- added) and also all specialized versions.
specialize :: ScEnv -> ScUsage -> (Var, SeqCoreCommand)
                    -> CoreM [(Var, SeqCoreCommand)]
specialize env (ScUsage calls used) (x, c)
  | skip
  = return [(x, c)]
  | otherwise
  = do
    -- Create the specializations
    specs <- mkSpecs
    -- Add specization rules to the function's identifier
    let x' = addRulesForSpecs specs
    -- Return the new binding along with all specialized bindings
    return $ (x', c) : map specToBinding specs
  where
    -- Create the specializations for the binding @let x = c@.
    mkSpecs :: CoreM [Spec]
    mkSpecs
      -- Find all calls made to this function
      | Just cs <- calls `lookupVarEnv` x
      = do
        -- Make a pattern for each call that we want to specialize for
        pats <- mapM callToPat (filter shouldSpec cs)
        -- Make a specialized function for each unique call pattern
        mapM specCall (nubBy samePat pats)
      | otherwise
      = return [] -- No calls made to this function

    {- 
     - The Paper gives 6 criteria for specialization, some of which must hold
     - or we wouldn't be here:
     -
     - H1 x is bound to a lambda
     - H2 c isn't too big
     - H3 The binding is recursive and the call is in its RHS (check)
     - H4 The call is saturated (check; see usageFromCut)
     - H5 At least one of the arguments is a constructor application
     - H6 That argument is case-analysed somewhere in the RHS
     -
     - Note that we're actually allowing mutual recursion, because we might
     - be here because there was a call here from some other function in the
     - same binding group. (This is refinement R4 in The Paper.)
     -
     - We can check H1 and H2 once for this variable x, so we do so in skip.
     - H5 and H6 are checked for each call by shouldSpec.
     -}

    -- | Decide whether to skip this binding altogether (i.e. check criteria
    -- H1 and H2).
    skip :: Bool
    skip | null binders
         = True -- H1 fails
         | Just sz <- sc_size env
         , not $ couldBeSmallEnoughToInline (sc_dflags env) sz
             (commandToCoreExpr body)
         = True -- H2 fails
         | otherwise
         = False

    binders :: [Var] -- ^ Binders for the bound function. Empty if not a function.
    body :: SeqCoreCommand -- ^ Body of the bound function after all lambdas.
    (binders, body) = collectLambdas c

    -- | Decide whether to specialize for a particular call (i.e. check
    -- criteria H5 and H6).
    shouldSpec :: Call -> Bool
    shouldSpec args
      = or $ zipWith qualifyingArg binders args
      where
        qualifyingArg x' arg
          = isSaturatedCtorApp arg && x' `elemVarSet` used

    -- | Create a specialization for a call pattern.
    specCall :: CallPat -> CoreM Spec
    specCall pat@(vars :-> vals)
      = do
        let c' = lambdas vars $
                  addLets (zipWith NonRec binders vals) body
        x' <- mkSysLocalM (fsLit "scsc") (commandType c')
        return $ Spec { spec_pat = pat, spec_id = x', spec_defn = c' }

    -- | Extract a call pattern, given the arguments in a call.
    callToPat :: Call -> CoreM CallPat
    callToPat args
      = do
        (varss, rhss) <- unzip `liftM` zipWithM argToSubpat binders args
        return $ concat varss :-> rhss

    -- | Given an argument to the call, abstract over it to produce part of a
    -- call pattern. This produces some number of pattern variables and one
    -- argument.
    argToSubpat :: Var -> SeqCoreCommand -> CoreM ([Var], SeqCoreCommand)
    argToSubpat var arg
      -- This is a saturated constructor application, so abstract over its
      -- arguments to produce the subpattern
      | Just (ctor, args, _) <- saturatedCtorApp arg
      = do
        -- Abstract over *term* arguments only
        let (tyArgs, tmArgs) = span isNontermArg args
        tmVars <- mapM (mkSysLocalM (fsLit "scsca") . commandType) tmArgs
        let cont = map App (tyArgs ++ map varCommand tmVars)
            cmd = Command { cmdValue = Var ctor
                          , cmdCont = cont
                          , cmdLet = [] }
        return (tmVars, cmd)
      -- Just abstract over the whole argument; it's either a variable or
      -- something like a function application, so specializing for it doesn't
      -- make sense
      | otherwise
      = do
        p <- mkSysLocalM (fsLit "scsca") (varType var)
        return ([p], varCommand p)

    -- | Produce a new version of the bound variable @x@, with a rule attached
    -- for each specialization.
    addRulesForSpecs :: [Spec] -> Var
    addRulesForSpecs specs
      = addIdSpecialisations x (zipWith ruleForSpec specs [1..])

    -- | Create the rewrite rule that activates the given specialization.
    ruleForSpec :: Spec -> Int -> CoreRule
    ruleForSpec (Spec { spec_pat = patVars :-> patArgs, spec_id = x' }) n
      = mkRule auto local name act fn bndrs args rhs
      where
        auto  = True
        local = True
        name  = mkFastString $ "SC:" ++ occNameString (nameOccName (idName x))
                  ++ show n
        act   = idInlineActivation x
        fn    = idName x
        bndrs = patVars
        args  = map commandToCoreExpr patArgs
        rhs   = commandToCoreExpr $
                  Command [] (Var x') (map (App . varCommand) patVars)
          
infix 4 `samePat`

samePat :: CallPat -> CallPat -> Bool
xs1 :-> cs1 `samePat` xs2 :-> cs2 =
  aeqIn env cs1 cs2
  where
    env = rnBndrs2 (mkRnEnv2 emptyInScopeSet) xs1 xs2
