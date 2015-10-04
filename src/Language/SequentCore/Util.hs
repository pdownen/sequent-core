-- | 
-- Module      : Language.SequentCore.Util
-- Description : Utilities used by the Sequent Core library
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental

module Language.SequentCore.Util (
  Maybes.orElse, consMaybe, mapAccumL2, mapAccumL3, mapWhileJust, pprTraceShort
) where

import DynFlags
import Maybes
import Outputable
import StaticFlags

import Data.List ( mapAccumL )

infixr 5 `consMaybe`

consMaybe :: Maybe a -> [a] -> [a]
Just x  `consMaybe` xs = x : xs
Nothing `consMaybe` xs = xs

mapWhileJust :: (a -> Maybe b) -> [a] -> ([b], [a])
mapWhileJust f (x : xs) | Just y <- f x = (y : ys, xs')
  where (ys, xs') = mapWhileJust f xs
mapWhileJust _ xs = ([], xs)


{-# INLINE mapAccumL2 #-}
mapAccumL2 :: (a -> b -> c -> (a, b, c)) -> a -> b -> [c] -> (a, b, [c])
mapAccumL2 f x y zs = (x', y', zs')
  where
    ((x', y'), zs') = mapAccumL f' (x, y) zs
    f' (a, b) c     = ((a', b'), c')
      where (a', b', c') = f a b c

{-# INLINE mapAccumL3 #-}
mapAccumL3 :: (a -> b -> c -> d -> (a, b, c, d)) -> a -> b -> c -> [d] -> (a, b, c, [d])
mapAccumL3 f x y z ws = (x', y', z', ws')
  where
    ((x', y', z'), ws') = mapAccumL f' (x, y, z) ws
    f' (a, b, c) d      = ((a', b', c'), d')
      where (a', b', c', d') = f a b c d

pprTraceShort :: String -> SDoc -> a -> a
-- ^ If debug output is on, show some 'SDoc' on the screen
pprTraceShort str doc x
   | opt_NoDebugOutput = x
   | otherwise         = pprAndThen unsafeGlobalDynFlags trace str
                          (withPprStyle shortStyle doc) x
   where
     shortStyle = mkUserStyle neverQualify (PartWay 3)
   
pprAndThen :: DynFlags -> (String -> a) -> String -> SDoc -> a
pprAndThen dflags kont heading pretty_msg
  = kont (showSDoc dflags doc)
    where
        doc = sep [text heading, nest 4 pretty_msg]
