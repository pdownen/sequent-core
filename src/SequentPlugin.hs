module SequentPlugin (plugin) where

import GhcPlugins ( Plugin(installCoreToDos), CommandLineOption
                  , defaultPlugin
                  , reinitializeGlobals
                  , CoreM, CoreToDo(CoreDoPluginPass)
                  , isBottomingId, idArity
                  , putMsg
                  , Var
                  )
import SequentCore

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos =
  do reinitializeGlobals
     return $ dump : todos ++ [dump]
  where dump = CoreDoPluginPass "sequent-core-no-op" (sequentPass showSequentCore)

showSequentCore :: [Bind Var] -> CoreM [Bind Var]
showSequentCore bs = do
  putMsg (ppr_binds_top bs)
  return bs

-- | Inline the continuation of a case into all of its branches.
inlineCaseCont :: Command b -> Maybe (Command b)
inlineCaseCont cmd =
  case cmdCont cmd of
    Case x t as : f : more ->
      Just cmd { cmdCont = Case x t (map inline as) : more }
      where
      inline (Alt ac xs c) = Alt ac xs (c { cmdCont = cmdCont c ++ [f] })

    _ -> Nothing


-- | Does this look like bottom
-- (i.e., a known bottom function applied to enough arguments)
commandIsBottom :: Command b -> Bool
commandIsBottom cmd =
  case cmdValue cmd of
    Var v -> isBottomingId v && contArgs (cmdCont cmd) >= idArity v
    _     -> False

-- | How many immediatly visible arguments we have in a continuation.
contArgs :: [Frame b] -> Int
contArgs fs =
  length [ () | App a <- takeWhile notCase fs, not (isTypeCommand a) ]
  where notCase (Case {}) = False
        notCase _         = True

-- | Does the argument to a function call look like a type?
--
-- Note: Arguments to function calls can be arbitrary computations
-- (i.e. commands).  To be well-formed, a command with a type for its
-- value should have an empty continuation, since we can't actually
-- *do* anything to a type.  If for some reason we are doing something
-- to a type (have a non-empty continuation), this command is
-- nonsensical so just return false.
isTypeCommand :: Command b -> Bool
isTypeCommand cmd = isTypeValue (cmdValue cmd) && null (cmdCont cmd)

-- | Does this value look like a type?
isTypeValue :: Value b -> Bool
isTypeValue (Type {}) = True
isTypeValue _         = False
