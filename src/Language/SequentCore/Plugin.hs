module Language.SequentCore.Plugin (
  -- | Tools for writing a GHC plugin using the Sequent Core language in place
  -- of GHC Core.

  sequentPass
) where

import Language.SequentCore.Syntax

import GhcPlugins (ModGuts, CoreM
                  , bindsOnlyPass
                  , deShadowBinds
                  )

-- | Given a function that processes a module's bindings as Sequent Core terms,
-- perform the same processing as a Core-to-Core pass usable from a GHC plugin.
-- Intended to be passed to the @CoreDoPluginPass@ constructor as part of your
-- plugin's @installCoreToDos@ function. See "Language.SequentCore.Dump" for an
-- example and the GHC manual for more details.
sequentPass :: ([SeqCoreBind] -> CoreM [SeqCoreBind])
            -- ^ A processing function. May assume that there are no shadowed
            -- identifiers in the given binders (this is ensured by a call to
            -- 'deShadowBinds').
            -> (ModGuts -> CoreM ModGuts)
sequentPass process =
  bindsOnlyPass (fmap toCoreBinds . process . fromCoreBinds . deShadowBinds)
