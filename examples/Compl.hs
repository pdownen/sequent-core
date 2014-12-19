{-# OPTIONS_GHC -fplugin=Language.SequentCore.Simpl -dcore-lint #-}

module Main (main, f) where

data Thing = Blue | Red Int | Orange Char deriving Show

f :: Int -> (Thing, Thing, Thing)
f x = let y = Red x
          z = Blue
      in
      let z = Orange 'Z'
          x = y
      in (x, y, z)

main = case f 10 of
  (f, g, h) -> print (h, g, f)
