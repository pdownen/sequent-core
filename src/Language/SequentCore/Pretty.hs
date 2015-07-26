{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      : Language.SequentCore.Pretty
-- Description : Pretty printing of Sequent Core terms
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Instances and functions for pretty-printing Sequent Core terms using GHC's
-- built-in pretty printer.
  
module Language.SequentCore.Pretty (
  pprTopLevelBinds
) where

import Language.SequentCore.Syntax

import qualified GhcPlugins as GHC
import Outputable
import PprCore ()

import Data.List

ppr_bind :: OutputableBndr b => Bind b -> SDoc
ppr_bind (NonRec pair) = ppr_binding pair
ppr_bind (Rec binds)   = hang (text "rec") 2 (vcat $ intersperse space $ ppr_block "{" ";" "}" (map ppr_binding binds))

ppr_binds_top :: OutputableBndr b => [Bind b] -> SDoc
ppr_binds_top binds = ppr_binds_with "" "" "" binds

-- | Print the given bindings as a sequence of top-level bindings.
pprTopLevelBinds :: OutputableBndr b => [Bind b] -> SDoc
pprTopLevelBinds = ppr_binds_top

ppr_block :: String -> String -> String -> [SDoc] -> [SDoc]
ppr_block open _ close [] = [text open <> text close]
ppr_block open mid close (first : rest)
  = text open <+> first : map (text mid <+>) rest ++ [text close]

ppr_binds :: OutputableBndr b => [Bind b] -> SDoc
ppr_binds binds = ppr_binds_with "{" ";" "}" binds

ppr_binds_with :: OutputableBndr b => String -> String -> String -> [Bind b] -> SDoc
ppr_binds_with open mid close binds = vcat $ intersperse space $ ppr_block open mid close (map ppr_bind binds)

ppr_binding :: OutputableBndr b => BindPair b -> SDoc
ppr_binding pair
  = pprBndr LetBind val_bdr $$
    hang (ppr val_bdr <+> equals) 2 body
  where
    val_bdr = binderOfPair pair
    body = either pprCoreTerm pprCorePKont (rhsOfPair pair)

ppr_comm :: OutputableBndr b => (SDoc -> SDoc) -> Command b -> SDoc
ppr_comm add_par comm
  = maybe_add_par $ ppr_let <+> ppr_cut
  where
    (binds, cut) = flattenCommand comm
    ppr_let
      | null binds = empty
      | otherwise  = hang (text "let") 2 (ppr_binds binds) $$ text "in"
    maybe_add_par = if null binds then noParens else add_par
    ppr_cut
      = case cut of
          Left (term, kont) -> cat [text "<" <> pprCoreTerm term,
                                    vcat $ ppr_block "|" ";" ">" $ ppr_kont_frames kont]
          Right (args, j)   -> sep [text "<jump", parens (sep $ punctuate comma (map pprCoreTerm args)),
                                    text "|", ppr j <> text ">"]

ppr_term :: OutputableBndr b => (SDoc -> SDoc) -> Term b -> SDoc
ppr_term _ (Var name) = ppr name
ppr_term add_par (Type ty) = add_par $ char '@' <+> ppr ty
ppr_term _ (Coercion _) = text "CO ..."
ppr_term add_par (Lit lit) = GHC.pprLiteral add_par lit
ppr_term add_par term@(Lam {})
  | Compute kbndr comm <- body
  = add_par $
      hang (char '\\' <+> sep (map (pprBndr LambdaBind) bndrs ++
                                [char '|', pprBndr LambdaBind kbndr]) <+> arrow)
        2 (pprCoreComm comm)
  | otherwise
  = add_par $
      hang (char '\\' <+> sep (map (pprBndr LambdaBind) bndrs) <+> arrow)
        2 (pprCoreTerm body)
  where
    (bndrs, body) = lambdas term
ppr_term add_par (Compute kbndr comm)
  = add_par $
      hang (text "compute" <+> pprBndr LambdaBind kbndr)
        2 (pprCoreComm comm)

ppr_kont_frames :: OutputableBndr b => Kont b -> [SDoc]
ppr_kont_frames (App v k)
  = char '$' <+> ppr_term noParens v : ppr_kont_frames k
ppr_kont_frames (Case var alts)
  = [hang (text "case as" <+> pprBndr LetBind var <+> text "of") 2 $
      vcat $ ppr_block "{" ";" "}" (map pprCoreAlt alts)]
ppr_kont_frames (Cast _ k)
  = text "cast ..." : ppr_kont_frames k
ppr_kont_frames (Tick _ k)
  = text "tick ..." : ppr_kont_frames k
ppr_kont_frames (Return k)
  = [text "ret" <+> ppr k]

ppr_kont :: OutputableBndr b => (SDoc -> SDoc) -> Kont b -> SDoc
ppr_kont add_par k
  | null frames
  = text "pass"
  | otherwise
  = add_par $ sep $ punctuate semi (ppr_kont_frames k)
  where frames = ppr_kont_frames k

ppr_pkont :: OutputableBndr b => (SDoc -> SDoc) -> PKont b -> SDoc
ppr_pkont add_par (PKont bndrs body)
  = add_par $
      hang (char '\\' <+> parens (sep (punctuate comma $ map (pprBndr LambdaBind) bndrs))
                      <+> arrow)
        2 (pprCoreComm body)

pprCoreAlt :: OutputableBndr b => Alt b -> SDoc
pprCoreAlt (Alt con args rhs)
 = hang (ppr_case_pat con args <+> arrow) 2 (pprCoreComm rhs)

ppr_case_pat :: OutputableBndr a => GHC.AltCon -> [a] -> SDoc
ppr_case_pat con args
  = ppr con <+> fsep (map ppr_bndr args)
  where
    ppr_bndr = pprBndr CaseBind

pprCoreComm :: OutputableBndr b => Command b -> SDoc
pprCoreComm comm = ppr_comm noParens comm

pprCoreTerm :: OutputableBndr b => Term b -> SDoc
pprCoreTerm val = ppr_term noParens val

pprCorePKont :: OutputableBndr b => PKont b -> SDoc
pprCorePKont pkont = ppr_pkont noParens pkont

noParens :: SDoc -> SDoc
noParens pp = pp

instance OutputableBndr b => Outputable (Bind b) where
  ppr = ppr_bind

instance OutputableBndr b => Outputable (BindPair b) where
  ppr = ppr_binding

instance OutputableBndr b => Outputable (Term b) where
  ppr = ppr_term noParens

instance OutputableBndr b => Outputable (Command b) where
  ppr = ppr_comm noParens

instance OutputableBndr b => Outputable (Kont b) where
  ppr = ppr_kont noParens
  
instance OutputableBndr b => Outputable (PKont b) where
  ppr = ppr_pkont noParens

instance OutputableBndr b => Outputable (Alt b) where
  ppr = pprCoreAlt
