module Main where

import qualified Data.Map as Map

type Id = String

data Prop
  = Var Id
  | Prop `And` Prop
  | Prop `Or` Prop
  | If Prop Prop
  | Not Prop

infixl 6 `Or`
infixl 7 `And`

type Env = Map.Map Id Bool

satisfy, falsify :: Prop -> Env -> (Env -> Bool) -> Bool

satisfy (Var x) env k
  = case Map.lookup x env of
      Just True -> k env
      Just False -> False
      Nothing -> k (Map.insert x True env)
satisfy (p `And` q) env k
  = satisfy p env $ \env' -> satisfy q env' k
satisfy (p `Or` q) env k
  = satisfy p env k || satisfy q env k
satisfy (Not p) env k
  = falsify p env k
satisfy (If p q) env k
  = satisfy (Not p `Or` q) env k

falsify (Var x) env k
  = case Map.lookup x env of
      Just True -> False
      Just False -> k env
      Nothing -> k (Map.insert x False env)
falsify (p `And` q) env k
  = falsify p env k || falsify q env k
falsify (p `Or` q) env k
  = falsify p env $ \env' -> falsify q env' k
falsify (Not p) env k
  = satisfy p env k
falsify (If p q) env k
  = falsify (Not p `Or` q) env k

satisfiable, falsifiable, valid :: Prop -> Bool

satisfiable p = satisfy p Map.empty (const True)
falsifiable p = falsify p Map.empty (const True)
valid = not . falsifiable

main = print [f p | f <- [satisfiable, falsifiable, valid]]
  where p = (Var "a" `Or` Var "b") `And` Not (Var "a")
