{-# OPTIONS_GHC -O0 -dcore-lint #-}

module Main (main, f) where

data Thing = Blue | Red Int | Orange Char deriving Show

f :: Int -> (Thing, Thing, Thing)
f x = let y f = Red f
          z = Blue
      in
      let z = Orange 'Z'
          x = y 7
      in (x, x, z)

main = case f 10 of
  (f, g, h) -> print (h, g, f)
