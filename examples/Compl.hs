{-# OPTIONS_GHC -O2 -dcore-lint #-}

module Main (main, f, odd) where

import Prelude hiding (odd)

data Thing = Blue | Red Int | Orange Char deriving Show

odd :: Int -> Bool
odd n = n `mod` 2 == 1

f :: Int -> (Thing, Thing, Thing)
f x = let y f | odd f = Red f
              | otherwise = Orange 'Q'
          z = Blue
      in
      if True then
        let z = Orange 'Z'
            x = y 7
        in (x, x, z)
      else (y 2, z, z)

main = case f 10 of
  (f, g, h) -> print (h, g, f)
