-- |
-- Module      : Language.SequentCore.Inspect
-- Description : Sequent Core information dumper
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- An optimizer plugin that reports specified information about the module from
-- a Sequent Core standpoint.

module Language.SequentCore.Inspect (
  plugin
) where

import GhcPlugins ( Plugin(installCoreToDos), CommandLineOption
                  , defaultPlugin
                  , reinitializeGlobals
                  , CoreM, CoreToDo(CoreDoPluginPass)
                  , putMsg, errorMsg
                  , getDynFlags, ufCreationThreshold
                  )

import Language.SequentCore.Simpl.ExprSize
import Language.SequentCore.Syntax
import Language.SequentCore.Plugin

import Outputable

import Control.Monad (forM_)

-- | The plugin. A GHC plugin is a module that exports a value called @plugin@
-- with the type 'Plugin'.
plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos =
  do reinitializeGlobals
     -- This puts the dump pass at the beginning of the pipeline, before any
     -- optimization. To see the post-optimizer state, put 'newPass' at the back
     -- of the list instead.
     return $ newPass : todos
  where
    newPass  = CoreDoPluginPass "sequent-core-inspect" passFunc
    passFunc = sequentPass (inspectSequentCore opts)

data Options = Options { optShowSizes :: Bool, optUnrecognized :: [String] }

defaults :: Options
defaults = Options { optShowSizes = False, optUnrecognized = [] }

parseOption :: String -> Options -> Options
parseOption "size" opts = opts { optShowSizes = True }
parseOption other  opts = opts { optUnrecognized = other : optUnrecognized opts }

inspectSequentCore :: [CommandLineOption] -> [SeqCoreBind] -> CoreM [SeqCoreBind]
inspectSequentCore rawOpts bs = do
  let opts        = foldr parseOption defaults rawOpts
      unknownOpts = optUnrecognized opts
  if null unknownOpts
    then do
      forM_ bs $ \bind -> case bind of
        NonRec pair -> showBind opts pair
        Rec pairs -> forM_ pairs (showBind opts)
    else do
      errorMsg $ text "Unrecognized option(s): " <+>
                   sep (punctuate comma $ map text unknownOpts)
  return bs

showBind :: Options -> SeqCoreBindPair -> CoreM ()
showBind opts pair
  = do
    dflags <- getDynFlags
    let (x, rhs) = destBindPair pair
        idPart = ppr x
        cap = ufCreationThreshold dflags
        sizePart | optShowSizes opts = ppr size
                 | otherwise         = empty
        size = either (termSize dflags cap) (kontSize dflags cap) rhs
    putMsg $ sep [ idPart, sizePart ]
  where
