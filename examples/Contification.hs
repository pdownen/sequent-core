{-# LANGUAGE MagicHash, GADTs #-}

module Main where

import GHC.Exts

case1 :: () -> Int#
case1 ()
  = let {-# NOINLINE k #-}
        k x = 1# +# x
    in k 3#

case2 :: () -> Int#
case2 ()
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
    in if k 3# then 1# else 2#
        
case2b :: () -> Int#
case2b ()
  = let {-# NOINLINE _k #-}
        _k f = f 1#
    in 3#

case3 :: Bool
case3
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
    in k (if k 3# then 1# else 2#)

{-# NOINLINE flag #-}
flag :: Bool
flag = False

case4 :: Bool
case4
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
        {-# NOINLINE g #-}
        g y = k (y 5#)
    in if flag && k 3# then True else g (+# 1#)

case5 :: Bool
case5
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
    in if flag then True else k 1#

data Stringy where Stringy :: a -> (a -> String) -> Stringy

{-# NOINLINE stringy #-}
stringy :: Stringy
stringy = Stringy (3 :: Int) show

case6 :: String
case6
  = let {-# NOINLINE k #-}
        k x = case x of { [] -> "Empty!"; s -> s }
        {-# NOINLINE g #-}
        g y f = k (f y)
    in case stringy of Stringy y f -> g y f

main :: IO ()
main = return ()
