module Language.SequentCore.Translate (
    valueFromCoreExpr, valueToCoreExpr, onCoreExpr
) where

import Language.SequentCore.Syntax

import qualified CoreSyn as Core

valueFromCoreExpr :: Core.CoreExpr -> SeqCoreValue
valueToCoreExpr :: SeqCoreValue -> Core.CoreExpr
onCoreExpr :: (SeqCoreValue -> SeqCoreValue) -> (Core.CoreExpr -> Core.CoreExpr)