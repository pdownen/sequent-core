module Language.SequentCore.Simpl.Monad (
  SimplM, SimplGlobalEnv(..), runSimplM, liftCoreM,
  getDynFlags, getMode, tick, freeTick
) where

import CoreMonad
import DynFlags  ( HasDynFlags(..) )
import Outputable

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class

newtype SimplM a = SimplM { unSimplM :: SimplGlobalEnv -> CoreM (a, SimplCount) }

data SimplGlobalEnv
  = SimplGlobalEnv { sg_mode :: SimplifierMode }

runSimplM :: SimplGlobalEnv -> SimplM a -> CoreM (a, SimplCount)
runSimplM genv m = unSimplM m genv

instance Monad SimplM where
  {-# INLINE return #-}
  return x = SimplM $
    \_ -> getDynFlags >>= \dflags -> return (x, zeroSimplCount dflags)

  {-# INLINE (>>=) #-}
  m >>= k
    = SimplM $ \mode -> do
        (x, count1) <- unSimplM m mode
        (y, count2) <- unSimplM (k x) mode
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
  = SimplM $ \_ -> withZeroCount m

instance HasDynFlags SimplM where
  getDynFlags = liftCoreM getDynFlags

instance MonadIO SimplM where
  liftIO = liftCoreM . liftIO

getMode :: SimplM SimplifierMode
getMode = SimplM $ \genv -> withZeroCount $ return (sg_mode genv)

tick, freeTick :: Tick -> SimplM ()
tick t
  = liftCoreM $ putMsg (text "I has a tick:" <+> ppr t) >> getDynFlags >>= \dflags ->
      addSimplCount (doSimplTick dflags t (zeroSimplCount dflags))

freeTick t 
  = liftCoreM $ getDynFlags >>= \dflags ->
      addSimplCount (doFreeSimplTick t (zeroSimplCount dflags))

withZeroCount :: CoreM a -> CoreM (a, SimplCount)
withZeroCount m = do
  x <- m
  dflags <- getDynFlags
  return (x, zeroSimplCount dflags)
