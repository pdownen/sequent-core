module Language.SequentCore.Simpl.Util (
  ArgInfo, tracing, traceTicks, dumping, linting
) where

import Outputable

data ArgInfo

instance Outputable ArgInfo

tracing, traceTicks, dumping, linting :: Bool
