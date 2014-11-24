-- | 
-- Module      : Language.SequentCore.Syntax
-- Description : Sequent Core syntax and translations
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- The AST for Sequent Core, with translations to and from GHC Core.

module Language.SequentCore.Syntax (
  -- * AST Types
  Value(..), Frame(..), Cont, Command(..), Bind(..), Alt(..),
  SeqCoreValue, SeqCoreFrame, SeqCoreCont, SeqCoreCommand, SeqCoreBind,
    SeqCoreAlt,
  -- * Constructors
  valueCommand, varCommand, lambdas, addLets,
  -- * Translation
  -- $txn
  fromCoreExpr, fromCoreBind, fromCoreBinds,
  commandToCoreExpr, valueToCoreExpr, frameToCoreExpr,
  bindToCore, bindsToCore, altToCore
) where

import GhcPlugins (Id, Literal, Type, Coercion, AltCon, Tickish, Var)

import qualified GhcPlugins as GHC

--------------------------------------------------------------------------------
-- AST Types
--------------------------------------------------------------------------------

-- | An atomic value. These include literals, lambdas, and variables, as well as
-- types and coercions (see GHC's 'GHC.Expr' for the reasoning).
data Value b    = Lit Literal       -- ^ A primitive literal value.
                | Lam b (Command b) -- ^ A function. The body is a computation,
                                    -- that is, a 'Command'.
                | Type Type         -- ^ A type. Used to pass a type as an
                                    -- argument to a type-level lambda.
                | Coercion Coercion -- ^ A coercion. Used to pass evidence
                                    -- to the @cast@ operation.
                | Var Id            -- ^ A term variable.

-- | A stack frame. A continuation is simply a list of these. Each represents
-- the outer part of a Haskell expression, with a "hole" where a value can be
-- placed. Computation in the sequent calculus is expressed as the interation of
-- a value with a continuation.
data Frame b    = App  {- expr -} (Command b)    -- ^ Apply the value to an
                                                 -- argument, which may be a
                                                 -- computation.
                | Case {- expr -} b Type [Alt b] -- ^ Perform case analysis on
                                                 -- the value.
                | Cast {- expr -} Coercion       -- ^ Cast the value using the
                                                 -- given proof.
                | Tick (Tickish Id) {- expr -}   -- ^ Annotate the enclosed
                                                 -- frame. Used by the profiler.

-- | A continuation, expressed as a list of 'Frame's. In terms of the sequent
-- calculus, here @nil@ stands for a free covariable; since Haskell does not
-- allow for control effects, we only allow for one covariable.
type Cont b     = [Frame b]

-- | A general computation. A command brings together a list of bindings, some
-- value, and a /continuation/ saying what to do with that value. The value and
-- continuation comprise a /cut/ in the sequent calculus.
data Command b  = Command { -- | Bindings surrounding the computation.
                            cmdLet   :: [Bind b]
                            -- | The value provided to the continuation.
                          , cmdValue :: Value b
                            -- | What to do with the value.
                          , cmdCont  :: Cont b
                          }

-- | A binding. Similar to the 'GHC.Bind' datatype from GHC. Can be either a
-- single non-recursive binding or a mutually recursive block.
data Bind b     = NonRec b (Command b) -- ^ A single non-recursive binding.
                | Rec [(b, Command b)] -- ^ A block of mutually recursive bindings.

-- | A case alternative. Given by the head constructor (or literal), a list of
-- bound variables (empty for a literal), and the body as a 'Command'.
data Alt b      = Alt AltCon [b] (Command b)

-- | Usual instance of 'Value', with 'Var's for binders
type SeqCoreValue   = Value   Var
-- | Usual instance of 'Frame', with 'Var's for binders
type SeqCoreFrame   = Frame   Var
-- | Usual instance of 'Cont', with 'Var's for binders
type SeqCoreCont    = Cont    Var
-- | Usual instance of 'Command', with 'Var's for binders
type SeqCoreCommand = Command Var
-- | Usual instance of 'Bind', with 'Var's for binders
type SeqCoreBind    = Bind    Var
-- | Usual instance of 'Alt', with 'Var's for binders
type SeqCoreAlt     = Alt     Var

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

-- | Constructs a command that simply returns a value.
valueCommand :: Value b -> Command b
valueCommand v = Command { cmdLet = [], cmdValue = v, cmdCont = [] }

-- | Constructs a command that simply returns a variable.
varCommand :: Id -> Command b
varCommand x = valueCommand (Var x)

-- | Constructs a number of lambdas surrounding a function body.
lambdas :: [b] -> Command b -> Command b
lambdas xs body = foldr (\x c -> valueCommand (Lam x c)) body xs

-- | Adds the given bindings outside those in the given command.
addLets :: [Bind b] -> Command b -> Command b
addLets bs c = c { cmdLet = bs ++ cmdLet c }

--------------------------------------------------------------------------------
-- Translation
--------------------------------------------------------------------------------

-- $txn
-- The translations to and from Sequent Core are /not/ guaranteed to be perfect
-- inverses. However, any differences between @e@ and @commandToCoreExpr
-- (fromCoreExpr e)@ should be operationally insignificant, such as a @let@
-- floating out from a function being applied. A more precise characterization
-- of the indended invariants of these functions would entail some sort of
-- /bisimulation/, but it should suffice to know that the translations are
-- "faithful enough."

-- | Translates a Core expression into Sequent Core.
fromCoreExpr :: GHC.Expr b -> Command b
fromCoreExpr = go [] []
  where
  val binds frames v =
    Command { cmdLet = binds, cmdCont = frames, cmdValue = v }

  go binds frames expr =
    case expr of
      GHC.Var x         -> val binds frames (Var x)
      GHC.Lit l         -> val binds frames (Lit l)
      GHC.App e1 e2     -> go binds (App (fromCoreExpr e2) : frames) e1
      GHC.Lam x e       -> val binds frames (Lam x (fromCoreExpr e))
      GHC.Let bs e      -> go (fromCoreBind bs : binds) frames e
      GHC.Case e x t as -> go binds (Case x t (map fromCoreAlt as) : frames) e
      GHC.Cast e co     -> go binds (Cast co : frames) e
      GHC.Tick ti e     -> go binds (Tick ti : frames) e
      GHC.Type t        -> val binds frames (Type t)
      GHC.Coercion co   -> val binds frames (Coercion co)

-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: GHC.Alt b -> Alt b
fromCoreAlt (ac, bs, e) = Alt ac bs (fromCoreExpr e)

-- | Translates a Core binding into Sequent Core.
fromCoreBind :: GHC.Bind b -> Bind b
fromCoreBind bind =
  case bind of
    GHC.NonRec b e -> NonRec b (fromCoreExpr e)
    GHC.Rec bs     -> Rec [ (b, fromCoreExpr e) | (b,e) <- bs ]

-- | Translates a list of Core bindings into Sequent Core.
fromCoreBinds :: [GHC.Bind b] -> [Bind b]
fromCoreBinds = map fromCoreBind

-- | Translates a command into Core.
commandToCoreExpr :: Command b -> GHC.Expr b
commandToCoreExpr cmd = foldl addLet baseExpr (cmdLet cmd)
  where
  addLet e b  = GHC.Let (bindToCore b) e
  baseExpr    = foldl (flip frameToCoreExpr)
                      (valueToCoreExpr (cmdValue cmd))
                      (cmdCont cmd)

-- | Translates a value into Core.
valueToCoreExpr :: Value b -> GHC.Expr b
valueToCoreExpr val =
  case val of
    Lit l       -> GHC.Lit l
    Lam b c     -> GHC.Lam b (commandToCoreExpr c)
    Type t      -> GHC.Type t
    Coercion co -> GHC.Coercion co
    Var x       -> GHC.Var x

-- | Translates a frame into a function that will wrap a Core expression with a
-- fragment of context (an argument to apply to, a case expression to run,
-- etc.).
frameToCoreExpr :: Frame b -> (GHC.Expr b -> GHC.Expr b)
frameToCoreExpr frame e =
  case frame of
    App  {- expr -} e2      -> GHC.App e (commandToCoreExpr e2)
    Case {- expr -} b t as  -> GHC.Case e b t (map altToCore as)
    Cast {- expr -} co      -> GHC.Cast e co
    Tick ti {- expr -}      -> GHC.Tick ti e

-- | Translates a binding into Core.
bindToCore :: Bind b -> GHC.Bind b
bindToCore bind =
  case bind of
    NonRec b c -> GHC.NonRec b (commandToCoreExpr c)
    Rec bs     -> GHC.Rec [ (b,commandToCoreExpr c) | (b,c) <- bs ]

-- | Translates a list of bindings into Core.
bindsToCore :: [Bind b] -> [GHC.Bind b]
bindsToCore = map bindToCore

-- | Translates a case alternative into Core.
altToCore :: Alt b -> GHC.Alt b
altToCore (Alt ac bs c) = (ac, bs, commandToCoreExpr c)
