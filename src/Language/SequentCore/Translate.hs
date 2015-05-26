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
  fromCoreModule,
  bindsToCore,
  commandToCoreExpr, valueToCoreExpr, contToCoreExpr
) where

import Language.SequentCore.Syntax

import qualified CoreSyn as Core
import qualified CoreUtils as Core
import DataCon
import FastString
import Id
import Maybes
import qualified MkCore as Core
import MonadUtils
import Name
import Outputable
import Type
import Unique
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

type FromCoreEnv = InScopeSet

-- FIXME Try and work around the apparent need for unsafePerformIO here.
{-# NOINLINE uniqSupply #-}
uniqSupply :: UniqSupply
uniqSupply = unsafePerformIO (mkSplitUniqSupply contIdTag) -- tag will mark as
                                                           -- continuation var

fresh :: MonadUnique m => InScopeSet -> Type -> FastString -> m (FromCoreEnv, Var)
fresh ins name ty
  = do
    tryVar <- mkSysLocalM ty name
    let var = uniqAway ins tryVar
    return (extendInScopeSet ins var, var)

type FromCoreM a = UniqSM a

runFromCoreM :: FromCoreM a -> a
runFromCoreM m = initUs_ uniqSupply m

-- | Translates a Core expression into Sequent Core.
fromCoreExpr :: FromCoreEnv -> Core.CoreExpr -> SeqCoreCont
                            -> FromCoreM SeqCoreCommand
fromCoreExpr = go []
  where
    go binds env expr cont = case expr of
      Core.Var x         -> done $ Var (lookupInScope env x `orElse` x)
      Core.Lit l         -> done $ Lit l
      Core.App e1 e2     ->
        do e2' <- fromCoreExprAsValue env e2 mkArgContId
           go binds env e1 (App e2' cont)
      Core.Lam x e       -> done =<< fromCoreLams env x e
      Core.Let bs e      ->
        do (env', bs') <- fromCoreBind env (Just cont) bs
           go (bs' : binds) env' e cont
      Core.Case e x t as
        | Return _ <- cont ->
          do as' <- mapM (fromCoreAlt env cont) as
             go binds env e $ Case x t as'
        | otherwise ->
          -- Translating a case naively can duplicate lots of code. Rather than
          -- copy the continuation for each branch, we stuff it into a let
          -- binding and copy only a Return to that binding.
          do let contTy = mkFunTy t (contType cont)
             (env', k) <- fresh env contTy (fsLit "*casek")
             as' <- mapM (fromCoreAlt env' (Return k)) as
             go (NonRec k (Cont cont) : binds) env' e $ Case x t as'
      Core.Coercion co   -> done $ Coercion co
      Core.Cast e co     -> go binds env e (Cast co cont)
      Core.Tick ti e     -> go binds env e (Tick ti cont)
      Core.Type t        -> done $ Type t
      where done value = return $ mkCommand (reverse binds) value cont

fromCoreLams :: FromCoreEnv -> Core.CoreBndr -> Core.CoreExpr
                            -> FromCoreM SeqCoreValue
fromCoreLams env x expr
  = Lam (x : xs) kid <$> fromCoreExpr env' body (Return kid)
  where
    (xs, body) = Core.collectBinders expr
    kid = mkLamContId kty
    kty = mkFunTy ty ty
    ty  = Core.exprType body
    env' = extendInScopeSetList env (x : kid : xs)

fromCoreExprAsValue :: FromCoreEnv -> Core.CoreExpr -> (Type -> Id)
                                   -> FromCoreM SeqCoreValue
fromCoreExprAsValue env expr mkId
  = do
    comm <- fromCoreExpr env' expr (Return k)
    return $ mkCompute k comm
  where
    k  = uniqAway env (mkId (mkFunTy ty ty))
    ty = Core.exprType expr
    env' = extendInScopeSet env k

fromCoreLamAsCont :: FromCoreEnv -> SeqCoreCont -> Core.CoreExpr -> FromCoreM SeqCoreCont
fromCoreLamAsCont env cont (Core.Lam b e)
  = outer e
    where
      outer :: Core.CoreExpr -> FromCoreM SeqCoreCont
      outer (Core.App (Core.Var k) e)
                                  | isContId k
                                  = inner e <*> pure (Return k)
      outer (Core.Case e b ty as) = inner e <*> (Case b ty <$>
                                      mapM (fromCoreAlt env' cont) as)
        where env'                = extendInScopeSet env b
      outer body                  = inner body <*> pure cont
    
      inner :: Core.CoreExpr -> FromCoreM (SeqCoreCont -> SeqCoreCont)
      inner (Core.Var x) | x == b = return $ \k -> k
      inner (Core.App e1 e2)      = do
                                    e2' <- fromCoreExprAsValue env e2 mkArgContId
                                    (. App e2') <$> inner e1
      inner (Core.Cast e co)      = (. Cast co) <$> inner e
      inner (Core.Tick ti e)      = (. Tick ti) <$> inner e
      inner other                 = pprPanic "fromCoreLamAsCont::inner" (ppr other)
fromCoreLamAsCont _env _cont other
  = pprPanic "fromCoreLamAsCont" (ppr other)

-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: FromCoreEnv -> SeqCoreCont -> Core.CoreAlt -> FromCoreM SeqCoreAlt
fromCoreAlt env cont (ac, bs, e)
  = do
    let env' = extendInScopeSetList env bs
    e' <- fromCoreExpr env' e cont
    return $ Alt ac bs e'

-- | Translates a Core binding into Sequent Core.
fromCoreBind :: FromCoreEnv -> Maybe SeqCoreCont -> Core.CoreBind
                            -> FromCoreM (FromCoreEnv, SeqCoreBind)
fromCoreBind env cont_maybe bind =
  case bind of
    Core.NonRec b e |  isContId b
                    -> do
                       let cont = cont_maybe `orElse` panic "fromCoreBind"
                       cont' <- fromCoreLamAsCont env' cont e
                       return (env', NonRec b (Cont cont'))
                    |  otherwise
                    -> do
                       val <- fromCoreExprAsValue env' e mkLetContId
                       return (env', NonRec b val)
      where env'    = extendInScopeSet env b
    Core.Rec pairs  -> do
                       pairs' <- forM pairs $ \(b, e) ->
                         (b,) <$> fromCoreExprAsValue env' e mkLetContId
                       return (env', Rec pairs')
      where env'    = extendInScopeSetList env (map fst pairs)

-- | Translates a list of Core bindings into Sequent Core.
fromCoreBinds :: FromCoreEnv -> [Core.CoreBind] -> FromCoreM [SeqCoreBind]
fromCoreBinds env binds
  = snd <$> mapAccumLM (\env' -> fromCoreBind env' Nothing) env binds

fromCoreModule :: [Core.CoreBind] -> [SeqCoreBind]
fromCoreModule binds = runFromCoreM $ fromCoreBinds emptyInScopeSet binds

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
    Cont _       -> error "valueToCoreExpr"

-- | Translates a continuation into a function that will wrap a Core expression
-- with a fragment of context (an argument to apply to, a case expression to
-- run, etc.).
contToCoreExpr :: ContId -> SeqCoreCont -> (Core.CoreExpr -> Core.CoreExpr)
contToCoreExpr retId k e =
  case k of
    App  {- expr -} v k'      -> contToCoreExpr retId k' $ Core.mkCoreApp e (valueToCoreExpr v)
    Case {- expr -} b t as    -> Core.Case e b t (map (altToCore retId) as)
    Cast {- expr -} co k'     -> contToCoreExpr retId k' $ Core.Cast e co
    Tick ti {- expr -} k'     -> contToCoreExpr retId k' $ Core.Tick ti e
    Return x
      | x == retId            -> e
      | otherwise             -> Core.mkCoreApp (Core.Var x) e

-- | Translates a binding into Core.
bindToCore :: Maybe ContId -> SeqCoreBind -> Core.CoreBind
bindToCore retId_maybe bind =
  case bind of
    NonRec b (Cont k) -> Core.NonRec b (Core.Lam x (k' (Core.Var x)))
      where 
        x     = setOneShotLambda $ contArgId argTy
        argTy = snd $ splitFunTy (idType b)
        retId = retId_maybe `orElse` panic "bind2C: top-level cont"
        k'    = contToCoreExpr retId k
    NonRec b v        -> Core.NonRec b (valueToCoreExpr v)
    Rec bs            -> Core.Rec [ (b, valueToCoreExpr v) | (b,v) <- bs ]

-- | Translates a list of top-level bindings into Core.
bindsToCore :: [SeqCoreBind] -> [Core.CoreBind]
bindsToCore binds = map (bindToCore Nothing) binds

altToCore :: ContId -> SeqCoreAlt -> Core.CoreAlt
altToCore retId (Alt ac bs c) = (ac, bs, commandToCoreExpr retId c)

-- HACK: We want our own namespace for "wired-in names." The nice way to do this
-- would be to add it to the Unique module, but we're a plugin. Fortunately,
-- someone else already needed the mkUnique backdoor ... but this may need to
-- change. 

mkContIdUnique, mkContArgIdUnique :: Int -> Unique
mkContIdUnique    = mkUnique contIdTag -- should be 'Q'
mkContArgIdUnique = mkUnique 'q'

lamContKey, argContKey, letContKey, contArgKey :: Unique
[lamContKey, argContKey, letContKey] = map mkContIdUnique [1..3]
contArgKey = mkContArgIdUnique 1

lamContName, argContName, letContName, contArgName :: Name
[lamContName, argContName, letContName, contArgName] =
  zipWith mkSystemVarName
    [lamContKey,    argContKey,    letContKey,    contArgKey]
    [fsLit "*lamk", fsLit "*argk", fsLit "*letk", fsLit "*karg"]

mkLamContId, mkArgContId, mkLetContId :: Type -> ContId
[mkLamContId, mkArgContId, mkLetContId]
  = map mkLocalId [lamContName, argContName, letContName]

contArgId :: Type -> Id
contArgId ty = mkLocalId contArgName ty
