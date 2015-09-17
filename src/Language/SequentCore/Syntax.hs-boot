{-# LANGUAGE KindSignatures #-}

module Language.SequentCore.Syntax (
  Term, Frame, End, Command, Bind, Alt,
  SeqCoreTerm, SeqCoreCommand, SeqCoreBind, SeqCoreAlt,

  mkCommand
) where

import Var ( Var )

data Term (b :: *)
data Frame (b :: *)
data End (b :: *)
data Command (b :: *)
data Bind (b :: *)
data Alt (b :: *)

type SeqCoreTerm    = Term    Var
type SeqCoreCommand = Command Var
type SeqCoreBind    = Bind    Var
type SeqCoreAlt     = Alt     Var

class HasId b

mkCommand :: HasId b => [Bind b] -> Term b -> [Frame b] -> End b -> Command b
