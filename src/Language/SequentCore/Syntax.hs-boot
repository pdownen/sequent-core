{-# LANGUAGE KindSignatures #-}

module Language.SequentCore.Syntax (
  Value, Frame, Cont, Command, Bind, Alt,
  SeqCoreValue, SeqCoreFrame, SeqCoreCont, SeqCoreCommand, SeqCoreBind,
    SeqCoreAlt,

  mkCommand
) where

import Var ( Var )

data Value (b :: *)
data Frame (b :: *)
type Cont b = [Frame b]
data Command (b :: *)
data Bind (b :: *)
data Alt (b :: *)

type SeqCoreValue   = Value   Var
type SeqCoreFrame   = Frame   Var
type SeqCoreCont    = Cont    Var
type SeqCoreCommand = Command Var
type SeqCoreBind    = Bind    Var
type SeqCoreAlt     = Alt     Var

mkCommand :: [Bind b] -> Value b -> Cont b -> Command b
