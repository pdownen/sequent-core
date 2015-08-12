{-# OPTIONS_GHC -O2 -dcore-lint #-}

module Main (main, f, odd, red3) where

import Prelude hiding (odd)

data Thing = Blue | Red Int | Orange Char deriving Show

odd :: Int -> Bool
odd n = n `mod` 2 == 1

red3 :: Thing
red3 = Red 3

f :: Int -> (Thing, Thing, Thing)
f x = let y f | odd f = Red f
              | otherwise = Orange 'Q'
          z = Blue
      in
      case red3 of
        Red _ ->
          let z = Orange 'Z'
              x = y 7
          in (x, x, z)
        _ -> (y 2, z, z)

main = case f 10 of
  (f, g, h) -> print (h, g, f)
