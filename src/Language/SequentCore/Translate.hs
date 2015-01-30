-- | 
-- Module      : Language.SequentCore.Translate
-- Description : Core \<-\> Sequent Core
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Translation between Sequent Core and native GHC Core.

module Language.SequentCore.Translate (
  -- $txn
  fromCoreExpr, fromCoreBind, fromCoreBinds, fromCoreAlt,
  commandToCoreExpr, valueToCoreExpr, contToCoreExpr,
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
fromCoreExpr = go [] Return
  where
  go binds cont expr =
    case expr of
      Core.Var x         -> done $ Var x
      Core.Lit l         -> done $ Lit l
      Core.App e1 e2     -> go binds (App (fromCoreExprAsValue e2) cont) e1
      Core.Lam x e       -> done $ Lam x (fromCoreExpr e)
      Core.Let bs e      -> go (fromCoreBind bs : binds) cont e
      Core.Case e x t as -> go binds (Case x t (map fromCoreAlt as) cont) e
      Core.Cast e co     -> go binds (Cast co cont) e
      Core.Tick ti e     -> go binds (Tick ti cont) e
      Core.Type t        -> done $ Type t
      Core.Coercion co   -> done $ Coercion co
    where done value = mkCommand (reverse binds) value cont

fromCoreExprAsValue :: Core.Expr b -> Value b
fromCoreExprAsValue = mkCompute . fromCoreExpr

-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: Core.Alt b -> Alt b
fromCoreAlt (ac, bs, e) = Alt ac bs (fromCoreExpr e)

-- | Translates a Core binding into Sequent Core.
fromCoreBind :: Core.Bind b -> Bind b
fromCoreBind bind =
  case bind of
    Core.NonRec b e -> NonRec b (fromCoreExprAsValue e)
    Core.Rec bs     -> Rec [ (b, fromCoreExprAsValue e) | (b,e) <- bs ]

-- | Translates a list of Core bindings into Sequent Core.
fromCoreBinds :: [Core.Bind b] -> [Bind b]
fromCoreBinds = map fromCoreBind

-- | Translates a command into Core.
commandToCoreExpr :: SeqCoreCommand -> Core.CoreExpr
commandToCoreExpr cmd = foldr addLet baseExpr (cmdLet cmd)
  where
  addLet b e  = mkCoreLet (bindToCore b) e
  baseExpr    = contToCoreExpr (cmdCont cmd) (valueToCoreExpr (cmdValue cmd))

-- | Translates a value into Core.
valueToCoreExpr :: SeqCoreValue -> Core.CoreExpr
valueToCoreExpr val =
  case val of
    Lit l       -> Core.Lit l
    Var x       -> Core.Var x
    Lam b v     -> Core.Lam b (commandToCoreExpr v)
    Cons ct as  -> mkCoreApps (Core.Var (dataConWorkId ct))
                              (map valueToCoreExpr as) 
    Type t      -> Core.Type t
    Coercion co -> Core.Coercion co
    Compute c   -> commandToCoreExpr c

-- | Translates a frame into a function that will wrap a Core expression with a
-- fragment of context (an argument to apply to, a case expression to run,
-- etc.).
contToCoreExpr :: SeqCoreCont -> (Core.CoreExpr -> Core.CoreExpr)
contToCoreExpr k e =
  case k of
    App  {- expr -} v k'      -> contToCoreExpr k' $ mkCoreApp e (valueToCoreExpr v)
    Case {- expr -} b t as k' -> contToCoreExpr k' $ Core.Case e b t (map altToCore as)
    Cast {- expr -} co k'     -> contToCoreExpr k' $ Core.Cast e co
    Tick ti {- expr -} k'     -> contToCoreExpr k' $ Core.Tick ti e
    Return                    -> e

-- | Translates a binding into Core.
bindToCore :: SeqCoreBind -> Core.CoreBind
bindToCore bind =
  case bind of
    NonRec b v -> Core.NonRec b (valueToCoreExpr v)
    Rec bs     -> Core.Rec [ (b, valueToCoreExpr v) | (b,v) <- bs ]

-- | Translates a list of bindings into Core.
bindsToCore :: [SeqCoreBind] -> [Core.CoreBind]
bindsToCore = map bindToCore

-- | Translates a case alternative into Core.
altToCore :: SeqCoreAlt -> Core.CoreAlt
altToCore (Alt ac bs c) = (ac, bs, commandToCoreExpr c)
