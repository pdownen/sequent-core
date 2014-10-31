module Language.SequentCore.Dump (
  -- | An example GHC optimizer plugin using Sequent Core. Simply translates the
  -- given Core code to Sequent Core, dumps it to the screen, then translates
  -- back. This allows inspection of the Sequent Core code for a module and also
  -- tests the translation functions. Note that translating to Sequent Core and
  -- back should give an /equivalent/ program, but it may vary slightly. The
  -- effects should be benign, such as a @let@ floating around in an expression
  -- (but never across a lambda).
  
  plugin
) where

import GhcPlugins ( Plugin(installCoreToDos), CommandLineOption
                  , defaultPlugin
                  , reinitializeGlobals
                  , CoreM, CoreToDo(CoreDoPluginPass)
                  , putMsg
                  )

import Language.SequentCore.Syntax
import Language.SequentCore.Plugin
import Language.SequentCore.Pretty (ppr_binds_top)

-- | The plugin. A GHC plugin is a module that exports a value called @plugin@
-- with the type 'Plugin'.
plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todos =
  do reinitializeGlobals
     -- This puts the dump pass at the end of the pipeline, after all
     -- optimization. To see the pre-optimizer state, put 'dump' at the front
     -- of the list instead.
     return $ todos ++ [dump]
  where dump = CoreDoPluginPass "sequent-core-no-op" (sequentPass showSequentCore)

showSequentCore :: [SeqCoreBind] -> CoreM [SeqCoreBind]
showSequentCore bs = do
  putMsg (ppr_binds_top bs)
  return bs
