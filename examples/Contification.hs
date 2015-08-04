{-# LANGUAGE MagicHash, GADTs, RankNTypes #-}

module Main where

import GHC.Exts

-- Obvious case for contification.
case1_yes :: () -> Int#
case1_yes ()
  = let {-# NOINLINE k #-}
        k x = 1# +# x
    in k 3#

-- Can't contify because k is called in non-tail position.
case2_no :: () -> Int#
case2_no ()
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
    in if k 3# then 1# else 2#

-- Won't contify because _k isn't used at all.
case2b_gone :: () -> Int#
case2b_gone ()
  = let {-# NOINLINE _k #-}
        _k f = f 1#
    in 3#

-- Can't contify because one call is in non-tail position
-- (even though the other is).
case3_no :: Bool
case3_no
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
    in k (if k 3# then 1# else 2#)

{-# NOINLINE flag #-}
flag :: Bool
flag = False

-- Can contify g but not k
case4_mixed :: Bool
case4_mixed
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
        {-# NOINLINE g #-}
        g y = k (y 5#)
    in if flag && k 3# then True else g (+# 1#)

-- Can contify; tail-called from one branch and not used in the other
case5_yes :: Bool
case5_yes
  = let {-# NOINLINE k #-}
        k x = case x of { 0# -> True; _ -> False }
    in if flag then True else k 1#

-- An existential type to make things interesting
data Stringy where Stringy :: a -> (a -> String) -> Stringy

{-# NOINLINE stringy #-}
stringy :: Stringy
stringy = Stringy (3 :: Int) show

-- Produces a polymorphic continuation
case6_yes :: String
case6_yes
  = let {-# NOINLINE k #-}
        k x = case x of { [] -> "Empty!"; s -> s }
        {-# NOINLINE g #-}
        g y f = k (f y)
    in case stringy of Stringy y f -> g y f

-- Produces a rather oddly typed polymorphic continuation
case7_yes :: String
case7_yes
  = let {-# NOINLINE k #-}
        k :: forall a. a -> forall b. b -> (a -> String) -> (b -> String) -> String
        k x y f g = f x ++ g y
    in case (stringy, stringy) of (Stringy x f, Stringy y g) -> k x y f g

-- Produces a continuation that is NOT polymorphic because it would be
-- ill-typed; also, the Void# should be gone
case8_yes :: [Int]
case8_yes
  = let {-# NOINLINE k #-}
        k :: forall a. Void# -> [a]
        k _ = []
    in k void#

main :: IO ()
main = return ()
