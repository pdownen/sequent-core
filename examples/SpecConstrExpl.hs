module Main where

import Prelude hiding (last, drop)

{-last :: [a] -> a
last [] = error "last"
last [x] = x
last (x : xs) = last xs-}

{-drop :: Int -> [a] -> [a]
drop 0 xs = xs
drop _ [] = []
drop n (x : xs) = drop (n-1) xs-}

{-
maybeFac :: Maybe Int -> Maybe Int
maybeFac Nothing = Nothing
maybeFac (Just 0) = Just 1
maybeFac (Just n) | Just n' <- maybeFac (Just (n-1)) = Just (n * n')
                  | otherwise = Nothing
-}

facOrNeg :: Either Int Int -> Int
facOrNeg (Left 0) = 1
facOrNeg (Left n) = n * facOrNeg (Left (n-1))
facOrNeg (Right n) = -n

main = putStrLn "stuff"
