{-# OPTIONS_HADDOCK hide #-}

-- | 
-- Module      : Language.SequentCore.Util
-- Description : Utilities used by the Sequent Core library
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental

module Language.SequentCore.Util (
  orElse, consMaybe 
) where

import Data.Maybe

infixr 4 `orElse`
infixr 5 `consMaybe`

orElse :: Maybe a -> a -> a
orElse = flip fromMaybe

consMaybe :: Maybe a -> [a] -> [a]
Just x  `consMaybe` xs = x : xs
Nothing `consMaybe` xs = xs
