{-# LANGUAGE MagicHash #-}

module Main where

import GHC.Exts

case1 :: () -> Int#
case1 ()
  = let {-# NOINLINE k #-}
        k x = 1# +# x -- doesn't translate as a continuation
    in k 3#

case2 :: () -> Int#
case2 ()
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False } -- translates ...
    in if k 3# then 1# else 2#                     -- ... but used as function
        
case2b :: () -> Int#
case2b ()
  = let {-# NOINLINE _k #-}
        _k f = f 1# -- translates as a continuation ...
    in 3#           -- ... but isn't used at all

case3 :: Bool
case3
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False } -- translates ...
    in k (if k 3# then 1# else 2#)                 -- ... but used inconsistently

{-# NOINLINE flag #-}
flag :: Bool
flag = False

case4 :: Bool
case4
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False } -- translates ...
        {-# NOINLINE g #-}
        g y = k (y 5#)                             -- as does this one ...
    in if flag && k 3# then True else g (+# 1#)            -- ... but k fails, cascading

case5 :: Bool
case5
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False } -- translates unconditionally ...
    in if flag then True else k 1#                -- ... and is used only as cont

main :: IO ()
main = return ()