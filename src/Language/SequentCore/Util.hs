-- | 
-- Module      : Language.SequentCore.Util
-- Description : Utilities used by the Sequent Core library
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental

module Language.SequentCore.Util (
  Maybes.orElse, consMaybe, pprTraceShort
) where

import DynFlags
import Maybes
import Outputable
import StaticFlags

infixr 5 `consMaybe`

consMaybe :: Maybe a -> [a] -> [a]
Just x  `consMaybe` xs = x : xs
Nothing `consMaybe` xs = xs

pprTraceShort :: String -> SDoc -> a -> a
-- ^ If debug output is on, show some 'SDoc' on the screen
pprTraceShort str doc x
   | opt_NoDebugOutput = x
   | otherwise         = pprAndThen unsafeGlobalDynFlags trace str doc x
   
pprAndThen :: DynFlags -> (String -> a) -> String -> SDoc -> a
pprAndThen dflags kont heading pretty_msg
  = kont (showSDoc dflags doc)
    where
        doc = sep [text heading, nest 4 pretty_msg]
