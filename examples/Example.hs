{-# OPTIONS_GHC -dcore-lint #-}

module Main where

import Prelude hiding (map)

fibs = 0 : 1 : zipWith (+) fibs (tail fibs)

fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

f :: Int -> Int
f x = if fib 100 > 10 then f (x + 1) else 0

main :: IO ()
main = if fib 10 == fibs !! 10 then putStrLn "Yay!" else putStrLn "Boo!"

sum :: [Int] -> Int
sum xs            = sum' 0 xs
  where
    sum' :: Int -> [Int] -> Int
    sum' a []     = a
    sum' a (x:xs) = sum' (a+x) xs
