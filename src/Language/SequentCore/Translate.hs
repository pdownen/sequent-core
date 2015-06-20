{-# LANGUAGE TupleSections #-}

-- | 
-- Module      : Language.SequentCore.Translate
-- Description : Core \<-\> Sequent Core
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Translation between Sequent Core and native GHC Core.

module Language.SequentCore.Translate (
  -- $txn
  fromCoreModule, valueFromCoreExpr,
  bindsToCore,
  commandToCoreExpr, valueToCoreExpr, contToCoreExpr,
  onCoreExpr, onSequentCoreValue
) where

import Language.SequentCore.Subst
import Language.SequentCore.Syntax
import Language.SequentCore.WiredIn

import qualified CoreSyn as Core
import qualified CoreUtils as Core
import DataCon
import FastString
import qualified CoreFVs as Core
import Id
import Maybes
import qualified MkCore as Core
import MonadUtils
import Outputable
import Type        hiding ( substTy )
import UniqSupply
import VarEnv

import Control.Monad
import System.IO.Unsafe (unsafePerformIO)

-- $txn
-- The translations to and from Sequent Core are /not/ guaranteed to be perfect
-- inverses. However, any differences between @e@ and @commandToCoreExpr
-- (fromCoreExpr e)@ should be operationally insignificant, such as a @let@
-- floating out from a function being applied. A more precise characterization
-- of the indended invariants of these functions would entail some sort of
-- /bisimulation/, but it should suffice to know that the translations are
-- "faithful enough."

-- Public interface for Core --> Sequent Core

-- | Translates a list of Core bindings into Sequent Core.
fromCoreModule :: [Core.CoreBind] -> [SeqCoreBind]
fromCoreModule binds = runFromCoreM $ fromCoreBinds emptySubst binds

-- | Translates a single Core expression as a Sequent Core value.
valueFromCoreExpr :: Core.CoreExpr -> SeqCoreValue
valueFromCoreExpr expr
  = runFromCoreM $ fromCoreExprAsValue freeVarSet expr mkLetContId
  where
    freeVarSet = mkSubst (mkInScopeSet (Core.exprFreeVars expr))
                   emptyVarEnv emptyVarEnv emptyVarEnv

type FromCoreEnv = Subst

-- FIXME Try and work around the apparent need for unsafePerformIO here.
{-# NOINLINE uniqSupply #-}
uniqSupply :: UniqSupply
uniqSupply = unsafePerformIO (mkSplitUniqSupply sequentCoreTag)

freshContId :: MonadUnique m => FromCoreEnv -> Type -> FastString -> m (FromCoreEnv, ContId)
freshContId env inTy name
  = do
    tryVar <- asContId `liftM` mkSysLocalM name inTy
    let var = uniqAway (substInScope env) tryVar
    return (extendInScope env var, var)

type FromCoreM a = UniqSM a

runFromCoreM :: FromCoreM a -> a
runFromCoreM m = initUs_ uniqSupply m

-- | Translates a Core expression into Sequent Core.
fromCoreExpr :: FromCoreEnv -> Core.CoreExpr -> SeqCoreCont
                            -> FromCoreM SeqCoreCommand
fromCoreExpr env expr cont = go [] env expr cont
  where
    go binds env expr cont = case expr of
      Core.Var x         -> done $ lookupIdSubst (text "fromCoreExpr") env x
      Core.Lit l         -> done $ Lit l
      Core.App (Core.Var k) e | Var k' <- lookupIdSubst (text "fromCoreExpr") env k, isContId k'
                         -> go binds env e (Return k')
      Core.App e1 e2     ->
        do e2' <- fromCoreExprAsValue env e2 mkArgContId
           go binds env e1 (App e2' cont)
      Core.Lam x e       -> done =<< fromCoreLams env x e
      Core.Let bs e      ->
        do (env', bs') <- fromCoreBind env (Just cont) bs
           go (bs' : binds) env' e cont
      Core.Case e x _ as
        | Return _ <- cont ->
          do let (env_rhs, x') = substBndr env x
             as' <- mapM (fromCoreAlt env_rhs cont) as
             go binds env e $ Case x' as'
        | otherwise ->
          -- Translating a case naively can duplicate lots of code. Rather than
          -- copy the continuation for each branch, we stuff it into a let
          -- binding and copy only a Return to that binding.
          do (env', k) <- freshContId env (contType cont) (fsLit "*casek")
             let (env_rhs, x') = substBndr env' x
             as' <- mapM (fromCoreAlt env_rhs (Return k)) as
             go (NonRec k (Cont cont) : binds) env' e $ Case x' as'
      Core.Coercion co   -> done $ Coercion (substCo env co)
      Core.Cast e co     -> go binds env e (Cast (substCo env co) cont)
      Core.Tick ti e     -> go binds env e (Tick (substTickish env ti) cont)
      Core.Type t        -> done $ Type (substTy env t)
      where done value = return $ mkCommand (reverse binds) value cont

fromCoreLams :: FromCoreEnv -> Core.CoreBndr -> Core.CoreExpr
                            -> FromCoreM SeqCoreValue
fromCoreLams env x expr
  = Lam xs' kid <$> fromCoreExpr env' body (Return kid)
  where
    (xs, body) = Core.collectBinders expr
    (env', xs') = substBndrs env (x : xs)
    kid = mkLamContId ty
    ty  = substTy env' (Core.exprType body)

fromCoreExprAsValue :: FromCoreEnv -> Core.CoreExpr -> (Type -> ContId)
                                   -> FromCoreM SeqCoreValue
fromCoreExprAsValue env expr mkId
  = do
    comm <- fromCoreExpr env' expr (Return k)
    return $ mkCompute k comm
  where
    k  = asContId $ uniqAway (substInScope env) (mkId ty)
    ty = substTy env (Core.exprType expr)
    env' = extendInScope env k

fromCoreLamAsCont :: FromCoreEnv -> SeqCoreCont -> Core.CoreExpr -> FromCoreM (Maybe SeqCoreCont)
fromCoreLamAsCont env cont (Core.Lam b e)
  = outer e
    where
      (env', b') = substBndr env b
      
      outer :: Core.CoreExpr -> FromCoreM (Maybe SeqCoreCont)
      outer (Core.App (Core.Var k) e)
                                  | Var k' <- lookupIdSubst (text "fromCoreLamAsCont::outer") env k
                                  , isContTy (idType k')
                                  = inner e (Return k')
      outer (Core.Case e b _ as)  = do
                                    let (env'', b') = substBndr env' b
                                    cont' <- Case b' <$> mapM (fromCoreAlt env'' cont) as
                                    inner e cont'
      outer body                  = inner body cont
    
      inner :: Core.CoreExpr -> SeqCoreCont -> FromCoreM (Maybe SeqCoreCont)
      inner (Core.Var x) k          | Var x' <- lookupIdSubst (text "fromCoreLamAsCont::inner") env' x
                                    , x' == b'
                                    = return (Just k)
      inner (Core.App e1 e2) k      = do
                                      e2' <- fromCoreExprAsValue env' e2 mkArgContId
                                      inner e1 (App e2' k)
      inner (Core.Cast e co) k      = inner e (Cast co k)
      inner (Core.Tick ti e) k      = inner e (Tick ti k)
      inner _                _      = return Nothing
fromCoreLamAsCont _env _cont other
  = pprPanic "fromCoreLamAsCont" (ppr other)

-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: FromCoreEnv -> SeqCoreCont -> Core.CoreAlt -> FromCoreM SeqCoreAlt
fromCoreAlt env cont (ac, bs, e)
  = do
    let (env', bs') = substBndrs env bs
    e' <- fromCoreExpr env' e cont
    return $ Alt ac bs' e'

-- | Translates a Core binding into Sequent Core.
fromCoreBind :: FromCoreEnv -> Maybe SeqCoreCont -> Core.CoreBind
                            -> FromCoreM (FromCoreEnv, SeqCoreBind)
fromCoreBind env cont_maybe bind =
  case bind of
    Core.NonRec b e |  -- If it's a continuation function, try translating as a
                       -- continuation
                       Just (inTy, _) <- splitContFunTy_maybe (idType b)
                       -- Make sure this isn't a top-level binding; if so, we can't
                       -- keep it as a continuation
                    ,  Just cont          <- cont_maybe
                    -> do
                       let (env', b') = substBndr env (b `setIdType` mkContTy inTy)
                       cont'_maybe <- fromCoreLamAsCont env' cont e
                       case cont'_maybe of
                         Just cont' -> return (env', NonRec b' (Cont cont'))
                         Nothing    -> asValue
                    |  otherwise
                    -> asValue
      where asValue =  do
                       let b' | Just (inTy, outTy) <- splitContFunTy_maybe (idType b)
                              = b `setIdType` mkFunTy inTy outTy
                              | otherwise
                              = b
                       let (env', b'') = substBndr env b'
                       val <- fromCoreExprAsValue env' e mkLetContId
                       return (env', NonRec b'' val)
    Core.Rec pairs  -> do
                       let (env', bs') = substRecBndrs env (map fst pairs)
                       vals' <- forM (map snd pairs) $ \e ->
                         fromCoreExprAsValue env' e mkLetContId
                       return (env', Rec (zip bs' vals'))

fromCoreBinds :: FromCoreEnv -> [Core.CoreBind] -> FromCoreM [SeqCoreBind]
fromCoreBinds env binds
  = snd <$> mapAccumLM (\env' -> fromCoreBind env' Nothing) env binds

-- | Translates a command into Core.
commandToCoreExpr :: ContId -> SeqCoreCommand -> Core.CoreExpr
commandToCoreExpr retId cmd = foldr addLet baseExpr (cmdLet cmd)
  where
  addLet b e = Core.mkCoreLet (bindToCore (Just retId) b) e
  baseExpr = contToCoreExpr retId (cmdCont cmd) (valueToCoreExpr (cmdValue cmd))

-- | Translates a value into Core.
valueToCoreExpr :: SeqCoreValue -> Core.CoreExpr
valueToCoreExpr val =
  case val of
    Lit l        -> Core.Lit l
    Var x        -> Core.Var x
    Lam xs kb c  -> Core.mkCoreLams xs (commandToCoreExpr kb c)
    Cons ct as   -> Core.mkCoreApps (Core.Var (dataConWorkId ct)) $ map valueToCoreExpr as
    Type t       -> Core.Type t
    Coercion co  -> Core.Coercion co
    Compute kb c -> commandToCoreExpr kb c
    Cont _       -> pprPanic "valueToCoreExpr" (ppr val)

-- | Translates a continuation into a function that will wrap a Core expression
-- with a fragment of context (an argument to apply to, a case expression to
-- run, etc.).
contToCoreExpr :: ContId -> SeqCoreCont -> (Core.CoreExpr -> Core.CoreExpr)
contToCoreExpr retId k e =
  case k of
    App  {- expr -} v k'      -> contToCoreExpr retId k' $ Core.mkCoreApp e (valueToCoreExpr v)
    Case {- expr -} b as      -> Core.Case e b (contTyArg (idType retId)) (map (altToCore retId) as)
    Cast {- expr -} co k'     -> contToCoreExpr retId k' $ Core.Cast e co
    Tick ti {- expr -} k'     -> contToCoreExpr retId k' $ Core.Tick ti e
    Return x
      | x == retId            -> e
      | otherwise             -> Core.mkCoreApp (Core.Var x') e
      where x' = contIdToCore retId x

contIdToCore :: Id -> ContId -> Id
contIdToCore retId k = k `setIdType` mkContFunTy argTy retTy
  where
    tyOf k = isContTy_maybe (idType k) `orElse` pprPanic "contIdToCore" (pprBndr LetBind k)
    argTy = tyOf k
    retTy = tyOf retId

-- | Translates a binding into Core.
bindToCore :: Maybe ContId -> SeqCoreBind -> Core.CoreBind
bindToCore retId_maybe bind =
  case bind of
    NonRec b (Cont k) -> Core.NonRec b' (Core.Lam x (k' (Core.Var x)))
      where
        b'    = contIdToCore retId b
        x     = setOneShotLambda $ mkContArgId argTy
        k'    = contToCoreExpr retId k
        argTy = isContTy_maybe (idType b) `orElse` pprPanic "bindToCore" (pprBndr LetBind b)
        retId = retId_maybe `orElse` panic "bindToCore: top-level cont"
    NonRec b v        -> Core.NonRec b (valueToCoreExpr v)
    Rec bs            -> Core.Rec [ (b, valueToCoreExpr v) | (b,v) <- bs ]

-- | Translates a list of top-level bindings into Core.
bindsToCore :: [SeqCoreBind] -> [Core.CoreBind]
bindsToCore binds = map (bindToCore Nothing) binds

altToCore :: ContId -> SeqCoreAlt -> Core.CoreAlt
altToCore retId (Alt ac bs c) = (ac, bs, commandToCoreExpr retId c)

-- Public interface for operations going in both directions

-- | Take an operation on Sequent Core values and perform it on Core expressions
onCoreExpr :: (SeqCoreValue -> SeqCoreValue) -> (Core.CoreExpr -> Core.CoreExpr)
onCoreExpr f = valueToCoreExpr . f . valueFromCoreExpr

-- | Take an operation on Core expressions and perform it on Sequent Core values
onSequentCoreValue :: (Core.CoreExpr -> Core.CoreExpr) -> (SeqCoreValue -> SeqCoreValue)
onSequentCoreValue f = valueFromCoreExpr . f . valueToCoreExpr