-- | 
-- Module      : Language.SequentCore.Util
-- Description : Utilities used by the Sequent Core library
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental

module Language.SequentCore.Util (
  Maybes.orElse, consMaybe 
) where

import Maybes

infixr 5 `consMaybe`

consMaybe :: Maybe a -> [a] -> [a]
Just x  `consMaybe` xs = x : xs
Nothing `consMaybe` xs = xs
