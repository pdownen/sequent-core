{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.SequentCore.Pretty (
  pprTopLevelBinds
) where

import {-# SOURCE #-} Language.SequentCore.Syntax

import Outputable
import PprCore ()

pprTopLevelBinds :: OutputableBndr b => [Bind b] -> SDoc

instance OutputableBndr b => Outputable (Bind b)
instance OutputableBndr b => Outputable (Value b)
instance OutputableBndr b => Outputable (Command b)
instance OutputableBndr b => Outputable (Cont b)
instance OutputableBndr b => Outputable (Alt b)
