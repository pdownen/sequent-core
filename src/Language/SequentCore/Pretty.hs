-- |
-- Module      : Language.SequentCore.Pretty
-- Description : Pretty printing of Sequent Core terms
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Instances and functions for pretty-printing Sequent Core terms using GHC's
-- built-in pretty printer.
  
module Language.SequentCore.Pretty (
  ppr_binds_top
) where

import Language.SequentCore.Syntax

import qualified GhcPlugins as GHC
import Outputable

import Data.List

ppr_bind :: OutputableBndr b => Bind b -> SDoc
ppr_bind (NonRec val_bdr expr) = ppr_binding (val_bdr, expr)
ppr_bind (Rec binds)           = hang (text "rec") 2 (vcat $ intersperse space $ ppr_block "{" ";" "}" (map ppr_binding binds))

-- | Print the given bindings as a sequence of top-level bindings.
ppr_binds_top :: OutputableBndr b => [Bind b] -> SDoc
ppr_binds_top binds = ppr_binds_with "" "" "" binds

ppr_block :: String -> String -> String -> [SDoc] -> [SDoc]
ppr_block open _ close [] = [text open <> text close]
ppr_block open mid close (first : rest)
  = text open <+> first : map (text mid <+>) rest ++ [text close]

ppr_binds :: OutputableBndr b => [Bind b] -> SDoc
ppr_binds binds = ppr_binds_with "{" ";" "}" binds

ppr_binds_with :: OutputableBndr b => String -> String -> String -> [Bind b] -> SDoc
ppr_binds_with open mid close binds = vcat $ intersperse space $ ppr_block open mid close (map ppr_bind binds)

ppr_binding :: OutputableBndr b => (b, Command b) -> SDoc
ppr_binding (val_bdr, expr)
  = pprBndr LetBind val_bdr $$
    hang (ppr val_bdr <+> equals) 2 (pprCoreComm expr)

ppr_comm :: OutputableBndr b => (SDoc -> SDoc) -> Command b -> SDoc
ppr_comm add_par comm
  = maybe_add_par $ ppr_let <+> cut (cmdValue comm) (cmdCont comm)
  where
    ppr_let
      = case cmdLet comm of
          [] -> empty
          binds -> hang (text "let") 2 (ppr_binds binds) $$ text "in"
    maybe_add_par = if null (cmdLet comm) then noParens else add_par
    cut val []
      = pprCoreValue val
    cut val frames
      = cat [text "<" <> pprCoreValue val, vcat $ ppr_block "|" ";" ">" $ map ppr_frame frames]

ppr_value :: OutputableBndr b => (SDoc -> SDoc) -> Value b -> SDoc
ppr_value _ (Var name) = ppr name
ppr_value add_par (Type ty) = add_par $ char '@' <+> ppr ty
ppr_value add_par (Coercion _) = add_par $ text "CO ..."
ppr_value add_par (Lit lit) = GHC.pprLiteral add_par lit
ppr_value add_par value@(Lam _ _)
  = let
      (bndrs, Just body) = collectBinders value
    in
      add_par $
      hang (char '\\' <+> sep (map (pprBndr LambdaBind) bndrs) <+> arrow)
          2 (pprCoreComm body)

collectBinders :: Value b -> ([b], Maybe (Command b))
collectBinders (Lam b comm)
  = go [b] comm
  where
    go bs (Command { cmdLet = [], cmdCont = [], cmdValue = Lam b' comm' })
      = go (b' : bs) comm'
    go bs comm'
      = (reverse bs, Just comm')
collectBinders _
  = ([], Nothing)

ppr_frame :: OutputableBndr b => Frame b -> SDoc
ppr_frame (App comm)
  = char '$' <+> pprParendComm comm
ppr_frame (Case var _ alts)
  = hang (text "case of" <+> pprBndr CaseBind var) 2 $
      vcat $ ppr_block "{" ";" "}" (map pprCoreAlt alts)
ppr_frame (Cast _)
  = text "cast ..."
ppr_frame (Tick _)
  = text "tick ..."

pprCoreAlt :: OutputableBndr b => Alt b -> SDoc
pprCoreAlt (Alt con args rhs)
 = hang (ppr_case_pat con args <+> arrow) 2 (pprCoreComm rhs)

ppr_case_pat :: OutputableBndr a => GHC.AltCon -> [a] -> SDoc
ppr_case_pat con args
  = ppr con <+> (fsep (map ppr_bndr args))
  where
    ppr_bndr = pprBndr CaseBind

pprParendComm, pprCoreComm :: OutputableBndr b => Command b -> SDoc
pprParendComm comm = ppr_comm parens comm
pprCoreComm comm = ppr_comm noParens comm

pprParendValue, pprCoreValue :: OutputableBndr b => Value b -> SDoc
pprParendValue val = ppr_value parens val
pprCoreValue val = ppr_value noParens val

noParens :: SDoc -> SDoc
noParens pp = pp

instance OutputableBndr b => Outputable (Bind b) where
  ppr = ppr_bind

instance OutputableBndr b => Outputable (Value b) where
  ppr = ppr_value noParens

instance OutputableBndr b => Outputable (Command b) where
  ppr = ppr_comm noParens

instance OutputableBndr b => Outputable (Frame b) where
  ppr = ppr_frame
