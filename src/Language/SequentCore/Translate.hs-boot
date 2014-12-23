module Language.SequentCore.Translate (
  fromCoreExpr, fromCoreBind, fromCoreBinds, fromCoreAlt,
  commandToCoreExpr, valueToCoreExpr, frameToCoreExpr,
  bindToCore, bindsToCore, altToCore
) where

import {-# SOURCE #-} Language.SequentCore.Syntax

import qualified CoreSyn as Core

fromCoreExpr  :: Core.Expr b -> Command b
fromCoreAlt   :: Core.Alt b -> Alt b
fromCoreBind  :: Core.Bind b -> Bind b
fromCoreBinds :: [Core.Bind b] -> [Bind b]

commandToCoreExpr :: SeqCoreCommand -> Core.CoreExpr
valueToCoreExpr   :: SeqCoreValue -> Core.CoreExpr
frameToCoreExpr   :: SeqCoreFrame -> (Core.CoreExpr -> Core.CoreExpr)
bindToCore        :: SeqCoreBind -> Core.CoreBind
bindsToCore       :: [SeqCoreBind] -> [Core.CoreBind]
altToCore         :: SeqCoreAlt -> Core.CoreAlt
