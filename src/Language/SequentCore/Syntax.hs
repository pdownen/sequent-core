module Language.SequentCore.Syntax (
  -- | The AST for Sequent Core, with translations to and from GHC Core.

  Value(..), Frame(..), Cont, Command(..), Bind(..), Alt(..),
  SeqCoreValue, SeqCoreFrame, SeqCoreCont, SeqCoreCommand, SeqCoreBind,
    SeqCoreAlt,
  fromCoreExpr, fromCoreBind, fromCoreBinds,
  commandToCoreExpr, valueToCoreExpr, frameToCoreExpr,
  toCoreBind, toCoreBinds, toCoreAlt
) where

import GhcPlugins (Id, Literal, Type, Coercion, AltCon, Tickish, Var)

import qualified GhcPlugins as GHC

--------------------------------------------------------------------------------
-- Sequent Calculus Based AST
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
                | Var Id            -- ^ A variable.

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
data Command b  = Command { cmdLet   :: [Bind b] -- ^ Bindings surrounding the
                                                 -- computation.
                          , cmdValue :: Value b  -- ^ The value provided to the
                                                 -- continuation.
                          , cmdCont  :: Cont b   -- ^ What to do with the value.
                          }

-- | A binding. Similar to the 'GHC.Bind' datatype from GHC. Can be either a
-- single non-recursive binding or a mutually recursive block.
data Bind b     = NonRec b (Command b)
                | Rec [(b, Command b)]

data Alt b      = Alt AltCon [b] (Command b)

type SeqCoreValue   = Value Var
type SeqCoreFrame   = Frame Var
type SeqCoreCont    = Cont Var
type SeqCoreCommand = Command Var
type SeqCoreBind    = Bind Var
type SeqCoreAlt     = Alt Var

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

fromCoreAlt :: GHC.Alt b -> Alt b
fromCoreAlt (ac, bs, e) = Alt ac bs (fromCoreExpr e)

fromCoreBind :: GHC.Bind b -> Bind b
fromCoreBind bind =
  case bind of
    GHC.NonRec b e -> NonRec b (fromCoreExpr e)
    GHC.Rec bs     -> Rec [ (b, fromCoreExpr e) | (b,e) <- bs ]

fromCoreBinds :: [GHC.Bind b] -> [Bind b]
fromCoreBinds = map fromCoreBind

commandToCoreExpr :: Command b -> GHC.Expr b
commandToCoreExpr cmd = foldl addLet baseExpr (cmdLet cmd)
  where
  addLet e b  = GHC.Let (toCoreBind b) e
  baseExpr    = foldl (flip frameToCoreExpr)
                      (valueToCoreExpr (cmdValue cmd))
                      (cmdCont cmd)

valueToCoreExpr :: Value b -> GHC.Expr b
valueToCoreExpr val =
  case val of
    Lit l       -> GHC.Lit l
    Lam b c     -> GHC.Lam b (commandToCoreExpr c)
    Type t      -> GHC.Type t
    Coercion co -> GHC.Coercion co
    Var x       -> GHC.Var x

frameToCoreExpr :: Frame b -> GHC.Expr b -> GHC.Expr b
frameToCoreExpr frame e =
  case frame of
    App  {- expr -} e2      -> GHC.App e (commandToCoreExpr e2)
    Case {- expr -} b t as  -> GHC.Case e b t (map toCoreAlt as)
    Cast {- expr -} co      -> GHC.Cast e co
    Tick ti {- expr -}      -> GHC.Tick ti e

toCoreBind :: Bind b -> GHC.Bind b
toCoreBind bind =
  case bind of
    NonRec b c -> GHC.NonRec b (commandToCoreExpr c)
    Rec bs     -> GHC.Rec [ (b,commandToCoreExpr c) | (b,c) <- bs ]

toCoreBinds :: [Bind b] -> [GHC.Bind b]
toCoreBinds = map toCoreBind

toCoreAlt :: Alt b -> GHC.Alt b
toCoreAlt (Alt ac bs c) = (ac, bs, commandToCoreExpr c)
