{-# LANGUAGE KindSignatures #-}

module Language.SequentCore.Syntax (
  Term, Cont, Command, Bind, Alt,
  SeqCoreTerm, SeqCoreCont, SeqCoreCommand, SeqCoreBind, SeqCoreAlt,

  mkCommand
) where

import Var ( Var )

data Term (b :: *)
data Cont (b :: *)
data Command (b :: *)
data Bind (b :: *)
data Alt (b :: *)

type SeqCoreTerm    = Term    Var
type SeqCoreCont    = Cont    Var
type SeqCoreCommand = Command Var
type SeqCoreBind    = Bind    Var
type SeqCoreAlt     = Alt     Var

class HasId b

mkCommand :: HasId b => [Bind b] -> Term b -> Cont b -> Command b
