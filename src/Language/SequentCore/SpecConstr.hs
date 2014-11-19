{-# LANGUAGE
    FlexibleInstances, PatternGuards, ScopedTypeVariables,
    ParallelListComp #-}

module Language.SequentCore.SpecConstr (plugin) where

import Language.SequentCore.Ops
import Language.SequentCore.Plugin
import Language.SequentCore.Pretty ()
import Language.SequentCore.Syntax

import CoreUnfold ( couldBeSmallEnoughToInline )
import CoreSyn    ( CoreRule )
import FastString ( fsLit, mkFastString )
import GhcPlugins ( Plugin(installCoreToDos), defaultPlugin, CoreM()
                  , putMsg, errorMsg
                  , reinitializeGlobals
                  , CoreToDo(CoreDoSpecConstr, CoreDoPasses, CoreDoPluginPass)
                  , DynFlags, getDynFlags, specConstrThreshold
                  )
import Id         ( Id, mkSysLocalM, idName, idInlineActivation )
import Name       ( nameOccName, occNameString )
import Outputable
import Rules      ( mkRule, addIdSpecialisations )
import Type       ( Type )
import UniqSupply
import Var        ( Var, varType, isTKVar )
import VarEnv
import VarSet

import Control.Applicative ((<$>), (<|>))
import Control.Monad
import Data.List (nubBy)
import Data.Monoid

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

class SpecConstr a where
  spec :: MonadUnique m => ScEnv -> a -> m (ScUsage, a)

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
  snd <$> spec env binds

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

instance SpecConstr SeqCoreValue where
  spec env (Lam x c)
    = do
      (usage, c') <- spec env' c
      return (usage, Lam x c')
    where
      env' = env { sc_how_bound = extendVarEnv hb x SpecArg }
      hb   = sc_how_bound env 
  spec _ v
    = return (emptyScUsage, v)

instance SpecConstr SeqCoreFrame where
  spec env (App c)
    = do
      (usage, c') <- spec env c
      return (usage, App c')
  spec env (Case x t as)
    = do
      (usage, as') <- spec env as
      return (usage, Case x t as')
  spec _ f
    = return (emptyScUsage, f)

instance SpecConstr SeqCoreCommand where
  spec env (Command { cmdLet = bs, cmdValue = v, cmdCont = fs })
    = specBinds env bs [] []
    where
      specBinds :: MonadUnique m
                => ScEnv -> [SeqCoreBind] -> [SeqCoreBind] -> [ScUsage]
                         -> m (ScUsage, SeqCoreCommand)
      specBinds env [] bs' usages
        = do
          (usage', v', fs') <- specCut env
          return (mconcat (usage' : usages), Command 
            { cmdLet = reverse bs', cmdValue = v', cmdCont = fs' })
      specBinds env (b : bs) bs' usages
        = do
          (usage', env', b') <- specBind env b
          specBinds env' bs (b' : bs') (usage' : usages)
      
      specCut :: MonadUnique m
              => ScEnv -> m (ScUsage, SeqCoreValue, SeqCoreCont)
      specCut env
        = do
          let u = usageFromCut env v fs
          (u_v, v') <- spec env v
          (u_fs, fs') <- spec env fs
          return (u `mappend` u_v `mappend` u_fs, v', fs')

usageFromCut :: ScEnv -> SeqCoreValue -> SeqCoreCont -> ScUsage
usageFromCut env (Var x) (Case {} : _)
  | Just SpecArg <- sc_how_bound env `lookupVarEnv` x
  = ScUsage emptyVarEnv (unitVarSet x)
usageFromCut env v@(Var f) fs
  | Just SpecFun <- sc_how_bound env `lookupVarEnv` f
  , Just (args, _) <- saturatedCall v fs
  = ScUsage (unitVarEnv f [args]) emptyVarSet
usageFromCut _ _ _
  = emptyScUsage

instance SpecConstr a => SpecConstr [a] where
  spec env as
    = do
      (us, as') <- unzip `liftM` mapM (spec env) as
      return (mconcat us, as')

specBind :: MonadUnique m
         => ScEnv -> SeqCoreBind -> m (ScUsage, ScEnv, SeqCoreBind)
specBind env (NonRec x c)
  = do
    (u, c') <- spec env c
    return (u, env, NonRec x c')
specBind env (Rec bs)
  = do
    (usages, cs') <- unzip `liftM` mapM (spec env' . snd) bs
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
            
specialize :: forall m. MonadUnique m
           => ScEnv -> ScUsage -> (Var, SeqCoreCommand)
           -> m [(Var, SeqCoreCommand)]
specialize env (ScUsage calls used) (x, c)
  | skip
  = return [(x, c)]
  | otherwise
  = do
    specs <- mkSpecs
    let x' = addRulesForSpecs specs
    return $ (x', c) : [ (spec_id s, spec_defn s) | s <- specs ]
  where
    mkSpecs :: m [Spec]
    mkSpecs
      | Just cs <- calls `lookupVarEnv` x
      = do
        pats <- mapM callToPat (filter shouldSpec cs)
        mapM specCall (nubBy samePat pats)
      | otherwise
      = return [] -- var not in env somehow??

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

    skip :: Bool
    skip | not $ isLambda c
         = True
         | Just sz <- sc_size env
         , not $ couldBeSmallEnoughToInline (sc_dflags env) sz
             (commandToCoreExpr c)
         = True
         | otherwise
         = False

    binders :: [Var]
    body :: SeqCoreCommand
    (binders, body) = collectLambdas c

    shouldSpec :: Call -> Bool
    shouldSpec args
      = or $ zipWith qualifyingArg binders args
      where
        qualifyingArg x' arg
          = isSaturatedCtorApp arg && x' `elemVarSet` used

    specCall :: CallPat -> m Spec
    specCall pat@(vars :-> vals)
      = do
        let c' = lambdas vars $
                  addLets [ NonRec b v | b <- binders | v <- vals ] body
        f <- mkSysLocalM (fsLit "scsc") (commandType c')
        return $ Spec pat f c'

    callToPat :: Call -> m CallPat
    callToPat args
      = do
        (varss, rhss) <- unzip `liftM` zipWithM argToSubpat binders args
        return $ concat varss :-> rhss

    argToSubpat :: Var -> SeqCoreCommand -> m ([Var], SeqCoreCommand)

    argToSubpat var c
      | Just (ctor, args, fs) <- saturatedCtorApp c
      = do
        -- Abstract over *term* arguments only
        let (tyArgs, tmArgs) = span isNontermArg args
        tmVars <- mapM (mkSysLocalM (fsLit "scsca") . commandType) tmArgs
        let cont = map App (tyArgs ++ map varCommand tmVars)
            cmd = Command { cmdValue = ctor
                          , cmdCont = cont
                          , cmdLet = [] }
        return (tmVars, cmd)
      | otherwise
      = do
        p <- mkSysLocalM (fsLit "scsca") (varType var)
        return ([p], varCommand p)

    addRulesForSpecs :: [Spec] -> Var
    addRulesForSpecs specs
      = addIdSpecialisations x (zipWith specAsRule specs [1..])

    specAsRule :: Spec -> Int -> CoreRule
    specAsRule (Spec { spec_pat = patVars :-> patArgs
                     , spec_id = x', spec_defn = c' }) n
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
          
samePat :: CallPat -> CallPat -> Bool
samePat (xs1 :-> cs1) (xs2 :-> cs2) = False -- TODO

instance SpecConstr SeqCoreAlt where
  spec env (Alt ac xs c)
    = do
      (usage, c') <- spec env c
      return (usage, Alt ac xs c')

instance SpecConstr SeqCoreBind where
  spec env b
    = do
      (u, _, b') <- specBind env b
      return (u, b')
