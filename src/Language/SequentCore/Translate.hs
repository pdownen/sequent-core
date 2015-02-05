-- | 
-- Module      : Language.SequentCore.Translate
-- Description : Core \<-\> Sequent Core
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Translation between Sequent Core and native GHC Core.

module Language.SequentCore.Translate (
  -- $txn
  fromCoreExpr, fromCoreBind, fromCoreBinds, fromCoreAlt,
  commandToCoreExpr, valueToCoreExpr, contToCoreExpr,
  bindToCore, bindsToCore, altToCore
) where

import Language.SequentCore.Syntax

import qualified CoreFVs as Core
import qualified CoreSyn as Core
import DataCon
import FastString
import Id
import qualified MkCore as Core
import Type
import TysWiredIn
import UniqSupply
import VarEnv

import Control.Applicative
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

-- | Translates a Core expression into Sequent Core.
fromCoreExpr :: Core.Expr b -> Command b
fromCoreExpr = go [] Return
  where
  go binds cont expr =
    case expr of
      Core.Var x         -> done $ Var x
      Core.Lit l         -> done $ Lit l
      Core.App e1 e2     -> go binds (App (fromCoreExprAsValue e2) cont) e1
      Core.Lam x e       -> done $ Lam x (fromCoreExpr e)
      Core.Let bs e      -> go (fromCoreBind bs : binds) cont e
      Core.Case e x t as -> go binds (Case x t (map fromCoreAlt as) cont) e
      Core.Cast e co     -> go binds (Cast co cont) e
      Core.Tick ti e     -> go binds (Tick ti cont) e
      Core.Type t        -> done $ Type t
      Core.Coercion co   -> done $ Coercion co
    where done value = mkCommand (reverse binds) value cont

fromCoreExprAsValue :: Core.Expr b -> Value b
fromCoreExprAsValue = mkCompute . fromCoreExpr

-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: Core.Alt b -> Alt b
fromCoreAlt (ac, bs, e) = Alt ac bs (fromCoreExpr e)

-- | Translates a Core binding into Sequent Core.
fromCoreBind :: Core.Bind b -> Bind b
fromCoreBind bind =
  case bind of
    Core.NonRec b e -> NonRec b (fromCoreExprAsValue e)
    Core.Rec bs     -> Rec [ (b, fromCoreExprAsValue e) | (b,e) <- bs ]

-- | Translates a list of Core bindings into Sequent Core.
fromCoreBinds :: [Core.Bind b] -> [Bind b]
fromCoreBinds = map fromCoreBind

-- FIXME There *has* to be a better way. But translation is a pure function and
-- is called from pure code, so no taking a UniqSupply as an argument. ????
{-# NOINLINE uniqSupply #-}
uniqSupply :: UniqSupply
uniqSupply = unsafePerformIO (mkSplitUniqSupply 'Q')

type ToCoreM a = UniqSM a

runToCoreM :: ToCoreM a -> a
runToCoreM m = initUs_ uniqSupply m

freshVar :: FastString -> Type -> Core.CoreExpr -> ToCoreM Id
freshVar name ty expr
  = do
    x <- mkSysLocalM name ty
    return $ uniqAway inScope x
  where
    inScope = mkInScopeSet $ Core.exprFreeIds expr

-- | Translates a command into Core.
commandToCoreExpr :: SeqCoreCommand -> Core.CoreExpr
commandToCoreExpr comm = runToCoreM $ comm2C comm

comm2C :: SeqCoreCommand -> ToCoreM Core.CoreExpr
comm2C cmd = do
  baseExpr <- cont2C (cmdCont cmd) <*> val2C (cmdValue cmd)
  foldM (\m b -> Core.mkCoreLet <$> bind2C b <*> pure m) baseExpr (cmdLet cmd)

-- | Translates a value into Core.
valueToCoreExpr :: SeqCoreValue -> Core.CoreExpr
valueToCoreExpr val = runToCoreM $ val2C val

val2C :: SeqCoreValue -> ToCoreM Core.CoreExpr
val2C val =
  case val of
    Lit l       -> return $ Core.Lit l
    Var x       -> return $ Core.Var x
    Lam b c     -> Core.Lam b <$> (comm2C c)
    Cons ct as  -> Core.mkCoreApps (Core.Var (dataConWorkId ct)) <$>
                                   (mapM val2C as) 
    Type t      -> return $ Core.Type t
    Coercion co -> return $ Core.Coercion co
    Compute c   -> comm2C c
    Cont _      -> error "valueToCoreExpr"

-- | Translates a frame into a function that will wrap a Core expression with a
-- fragment of context (an argument to apply to, a case expression to run,
-- etc.).
contToCoreExpr :: SeqCoreCont -> (Core.CoreExpr -> Core.CoreExpr)
contToCoreExpr k = runToCoreM $ cont2C k

cont2C :: SeqCoreCont -> ToCoreM (Core.CoreExpr -> Core.CoreExpr)
cont2C k =
  case k of
    App  {- expr -} v k       -> do
      k' <- cont2C k
      v' <- val2C v
      return $ \m -> k' (Core.mkCoreApp m v')
    Case {- expr -} b t as k  -> do
      k' <- cont2C k
      as' <- mapM alt2C as
      return $ \m -> k' (Core.Case m b t as')
    Cast {- expr -} co k      -> do
      k' <- cont2C k
      return $ \m -> k' (Core.Cast m co)
    Tick ti {- expr -} k      -> do
      k' <- cont2C k
      return $ \m -> k' (Core.Tick ti m)
    Jump x                    -> return $ \m -> Core.mkCoreApp (Core.Var x) m
    Return                    -> return id

-- | Translates a binding into Core.
bindToCore :: SeqCoreBind -> Core.CoreBind
bindToCore bind = runToCoreM $ bind2C bind

bind2C :: SeqCoreBind -> ToCoreM Core.CoreBind
bind2C bind =
  case bind of
    NonRec b (Cont k) -> do
      k' <- cont2C k
      -- We need to put something in the hole just to compute the free variables.
      -- Note that fakeExpr may be ill-typed (and probably is)!
      let fakeExpr = k' (Core.Var unitDataConId)
      x <- setOneShotLambda <$> freshVar (fsLit "karg") (idType b) fakeExpr
      return $ Core.NonRec b (Core.Lam x (k' (Core.Var x)))
    NonRec b v        -> Core.NonRec b <$> val2C v
    Rec bs            -> Core.Rec <$> mapM doPair bs
      where doPair (b, v) = val2C v >>= \v' -> return (b, v')

-- | Translates a list of bindings into Core.
bindsToCore :: [SeqCoreBind] -> [Core.CoreBind]
bindsToCore binds = runToCoreM $ binds2C binds

binds2C :: [SeqCoreBind] -> ToCoreM [Core.CoreBind]
binds2C = mapM bind2C

-- | Translates a case alternative into Core.
altToCore :: SeqCoreAlt -> Core.CoreAlt
altToCore alt = runToCoreM $ alt2C alt

alt2C :: SeqCoreAlt -> ToCoreM Core.CoreAlt
alt2C (Alt ac bs c) = comm2C c >>= \c' -> return (ac, bs, c')
