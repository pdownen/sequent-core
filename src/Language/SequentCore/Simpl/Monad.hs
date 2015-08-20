module Language.SequentCore.Simpl.Monad (
  SimplM, runSimplM, liftCoreM,
  getDynFlags, tick, freeTick, checkedTick
) where

import CoreMonad
import DynFlags  ( HasDynFlags(..) )
import Outputable
import UniqSupply

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class

traceTicks :: Bool
traceTicks = False

newtype SimplM a = SimplM { unSimplM :: CoreM (a, SimplCount) }

runSimplM :: SimplM a -> CoreM (a, SimplCount)
runSimplM m
  = do
    ans <- unSimplM m
    addSimplCount (snd ans)
    return ans

instance Monad SimplM where
  {-# INLINE return #-}
  return x = SimplM $
    getDynFlags >>= \dflags -> return (x, zeroSimplCount dflags)

  {-# INLINE (>>=) #-}
  m >>= k
    = SimplM $ do
        (x, count1) <- unSimplM m
        (y, count2) <- unSimplM (k x)
        let count = count1 `plusSimplCount` count2
        return $ count `seq` (y, count)

instance Functor SimplM where
  {-# INLINE fmap #-}
  fmap = liftM

instance Applicative SimplM where
  {-# INLINE pure #-}
  pure = return

  {-# INLINE (<*>) #-}
  (<*>) = ap

{-# INLINE liftCoreM #-}
liftCoreM :: CoreM a -> SimplM a
liftCoreM m
  = SimplM $ withZeroCount m

instance HasDynFlags SimplM where
  getDynFlags = liftCoreM getDynFlags

instance MonadIO SimplM where
  liftIO = liftCoreM . liftIO

instance MonadUnique SimplM where
  getUniqueSupplyM = liftCoreM getUniqueSupplyM
  getUniqueM = liftCoreM getUniqueM
  getUniquesM = liftCoreM getUniquesM

tick, freeTick, checkedTick :: Tick -> SimplM ()
tick t
  = SimplM $ do
      when traceTicks $ putMsg (text "TICK:" <+> ppr t)
      dflags <- getDynFlags
      let count = doSimplTick dflags t (zeroSimplCount dflags)
      return ((), count)

freeTick t
  = SimplM $ do
      when traceTicks $ putMsg (text "TICK (free):" <+> ppr t)
      dflags <- getDynFlags
      let count = doFreeSimplTick t (zeroSimplCount dflags)
      return ((), count)

-- TODO Implement tick limit
checkedTick = tick

withZeroCount :: CoreM a -> CoreM (a, SimplCount)
withZeroCount m = do
  x <- m
  dflags <- getDynFlags
  return (x, zeroSimplCount dflags)
