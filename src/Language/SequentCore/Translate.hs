module Language.SequentCore.Translate (
  -- $txn
  fromCoreExpr, fromCoreBind, fromCoreBinds, fromCoreAlt,
  commandToCoreExpr, valueToCoreExpr, frameToCoreExpr,
  bindToCore, bindsToCore, altToCore
) where

import Language.SequentCore.Syntax

import qualified CoreSyn as Core
import DataCon
import MkCore

-- $txn
-- The translations to and from Sequent Core are /not/ guaranteed to be perfect
-- inverses. However, any differences between @e@ and @commandToCoreExpr
-- (fromCoreExpr e)@ should be operationally insignificant, such as a @let@
-- floating out from a function being applied. A more precise characterization
-- of the indended invariants of these functions would entail some sort of
-- /bisimulation/, but it should suffice to know that the translations are
-- "faithful enough."

-- | Translates a Core expression into Sequent Core.
fromCoreExpr :: Core.Expr b -> Command b
fromCoreExpr = go [] []
  where
  go binds frames expr =
    case expr of
      Core.Var x         -> mkCommand binds (Var x) frames 
      Core.Lit l         -> mkCommand binds (Lit l) frames
      Core.App e1 e2     -> go binds (App (fromCoreExpr e2) : frames) e1
      Core.Lam x e       -> mkCommand binds (Lam x (fromCoreExpr e)) frames
      Core.Let bs e      -> go (fromCoreBind bs : binds) frames e
      Core.Case e x t as -> go binds (Case x t (map fromCoreAlt as) : frames) e
      Core.Cast e co     -> go binds (Cast co : frames) e
      Core.Tick ti e     -> go binds (Tick ti : frames) e
      Core.Type t        -> mkCommand binds (Type t) frames
      Core.Coercion co   -> mkCommand binds (Coercion co) frames

-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: Core.Alt b -> Alt b
fromCoreAlt (ac, bs, e) = Alt ac bs (fromCoreExpr e)

-- | Translates a Core binding into Sequent Core.
fromCoreBind :: Core.Bind b -> Bind b
fromCoreBind bind =
  case bind of
    Core.NonRec b e -> NonRec b (fromCoreExpr e)
    Core.Rec bs     -> Rec [ (b, fromCoreExpr e) | (b,e) <- bs ]

-- | Translates a list of Core bindings into Sequent Core.
fromCoreBinds :: [Core.Bind b] -> [Bind b]
fromCoreBinds = map fromCoreBind

-- | Translates a command into Core.
commandToCoreExpr :: SeqCoreCommand -> Core.CoreExpr
commandToCoreExpr cmd = foldl addLet baseExpr (cmdLet cmd)
  where
  addLet e b  = mkCoreLet (bindToCore b) e
  baseExpr    = foldl (flip frameToCoreExpr)
                      (valueToCoreExpr (cmdValue cmd))
                      (cmdCont cmd)

-- | Translates a value into Core.
valueToCoreExpr :: SeqCoreValue -> Core.CoreExpr
valueToCoreExpr val =
  case val of
    Lit l       -> Core.Lit l
    Var x       -> Core.Var x
    Lam b c     -> Core.Lam b (commandToCoreExpr c)
    Cons ct as  -> mkCoreApps (Core.Var (dataConWorkId ct))
                              (map commandToCoreExpr as) 
    Type t      -> Core.Type t
    Coercion co -> Core.Coercion co

-- | Translates a frame into a function that will wrap a Core expression with a
-- fragment of context (an argument to apply to, a case expression to run,
-- etc.).
frameToCoreExpr :: SeqCoreFrame -> (Core.CoreExpr -> Core.CoreExpr)
frameToCoreExpr frame e =
  case frame of
    App  {- expr -} e2      -> mkCoreApp e (commandToCoreExpr e2)
    Case {- expr -} b t as  -> Core.Case e b t (map altToCore as)
    Cast {- expr -} co      -> Core.Cast e co
    Tick ti {- expr -}      -> Core.Tick ti e

-- | Translates a binding into Core.
bindToCore :: SeqCoreBind -> Core.CoreBind
bindToCore bind =
  case bind of
    NonRec b c -> Core.NonRec b (commandToCoreExpr c)
    Rec bs     -> Core.Rec [ (b,commandToCoreExpr c) | (b,c) <- bs ]

-- | Translates a list of bindings into Core.
bindsToCore :: [SeqCoreBind] -> [Core.CoreBind]
bindsToCore = map bindToCore

-- | Translates a case alternative into Core.
altToCore :: SeqCoreAlt -> Core.CoreAlt
altToCore (Alt ac bs c) = (ac, bs, commandToCoreExpr c)
