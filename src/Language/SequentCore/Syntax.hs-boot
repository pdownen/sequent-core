{-# LANGUAGE KindSignatures #-}

module Language.SequentCore.Syntax (
  Value, Cont, Command, Bind, Alt,
  SeqCoreValue, SeqCoreCont, SeqCoreCommand, SeqCoreBind, SeqCoreAlt,

  mkCommand
) where

import Var ( Var )

data Value (b :: *)
data Cont (b :: *)
data Command (b :: *)
data Bind (b :: *)
data Alt (b :: *)

type SeqCoreValue   = Value   Var
type SeqCoreCont    = Cont    Var
type SeqCoreCommand = Command Var
type SeqCoreBind    = Bind    Var
type SeqCoreAlt     = Alt     Var

mkCommand :: [Bind b] -> Value b -> Cont b -> Command b
