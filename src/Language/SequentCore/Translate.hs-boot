module Language.SequentCore.Translate (
    termFromCoreExpr, termToCoreExpr, onCoreExpr
) where

import Language.SequentCore.Syntax

import qualified CoreSyn as Core

termFromCoreExpr :: Core.CoreExpr -> SeqCoreTerm
termToCoreExpr :: SeqCoreTerm -> Core.CoreExpr
onCoreExpr :: (SeqCoreTerm -> SeqCoreTerm) -> (Core.CoreExpr -> Core.CoreExpr)