{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -dcore-lint #-}

module Main where

import GHC.Exts ( Int#, Int(I#) )
import Prelude

anInt :: Int
anInt = 42

anInt# :: () -> Int#
anInt# = \() -> 42#

anIntFromI# :: Int
anIntFromI# = I# 42#

thing1 :: Bool -> Int -> Int
thing1 b n = if b then n else 0

thing2 :: Bool -> Int -> Maybe Int
thing2 b n = if b then Just n else Nothing

-- This next one gets *much* smaller after > is inlined (base goes down and n
-- gets an argument discount)
thing3 :: Bool -> Int -> Maybe Int
thing3 b n | b, n > 2 = Just n
           | otherwise = Nothing

main = return ()
