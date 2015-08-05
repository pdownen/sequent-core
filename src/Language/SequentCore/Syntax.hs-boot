{-# LANGUAGE KindSignatures #-}

module Language.SequentCore.Syntax (
  Term, Kont, Frame, End, Command, Bind, Alt,
  SeqCoreTerm, SeqCoreKont, SeqCoreCommand, SeqCoreBind, SeqCoreAlt,

  mkCommand
) where

import Var ( Var )

data Term (b :: *)
data Kont (b :: *)
data Frame (b :: *)
data End (b :: *)
data Command (b :: *)
data Bind (b :: *)
data Alt (b :: *)

type SeqCoreTerm    = Term    Var
type SeqCoreKont    = Kont    Var
type SeqCoreCommand = Command Var
type SeqCoreBind    = Bind    Var
type SeqCoreAlt     = Alt     Var

class HasId b

mkCommand :: HasId b => [Bind b] -> Term b -> Kont b -> Command b
