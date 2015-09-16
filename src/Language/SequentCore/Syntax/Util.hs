-- | 
-- Module      : Language.SequentCore.Syntax.Util
-- Description : More operations on Sequent Core syntax
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Utility functions on Sequent Core syntax. These are general-purpose but less
-- commonly used than the functions in 'Language.SequentCore.Syntax'.

module Language.SequentCore.Syntax.Util (
  -- * Case alternatives
  cmpAlt, ltAlt, findDefault, findAlt, mergeAlts, trimConArgs, filterAlts,
  
  -- * Size (for stats)
  seqCoreBindsSize,
  
  -- * Eta-reduction
  tryEtaReduce,
  
  -- * Free variables
  termFreeVars
) where

import Language.SequentCore.Syntax
import Language.SequentCore.Translate

import Coercion
import CoreFVs   ( exprFreeVars )
import CoreSyn   ( cmpAltCon, isEvaldUnfolding, Tickish(..) )
import CoreUtils ( dataConRepInstPat )
import DataCon
import Id
import IdInfo
import Outputable
import TyCon
import Type
import Unique
import Util      ( debugIsOn
                 , count, dropList, filterOut )
import Var
import VarSet

import Control.Applicative ( (<$>) )
import Control.Exception ( assert )

import Data.List
import Data.Maybe

-----------------------
-- Case alternatives --
-----------------------

cmpAlt :: Alt b -> Alt b -> Ordering
cmpAlt (Alt con1 _ _) (Alt con2 _ _) = con1 `cmpAltCon` con2

ltAlt :: Alt b -> Alt b -> Bool
ltAlt a1 a2 = (a1 `cmpAlt` a2) == LT

-- | Extract the default case alternative
findDefault :: [Alt b] -> ([Alt b], Maybe (Command b))
findDefault (Alt DEFAULT args rhs : alts) = assert (null args) (alts, Just rhs)
findDefault alts                          =                    (alts, Nothing)

-- | Find the case alternative corresponding to a particular
-- constructor: Nothing if no such constructor exists
findAlt :: AltCon -> [Alt b] -> Maybe (Alt b)
    -- A "Nothing" result *is* legitmiate
    -- See Note [Unreachable code]
findAlt con alts
  = case alts of
        (deflt@(Alt DEFAULT _ _):alts) -> go alts (Just deflt)
        _                              -> go alts Nothing
  where
    go []                     deflt = deflt
    go (alt@(Alt con1 _ _) : alts) deflt
      = case con `cmpAltCon` con1 of
          LT -> deflt   -- Missed it already; the alts are in increasing order
          EQ -> Just alt
          GT -> assert (con1 /= DEFAULT) $ go alts deflt

---------------------------------
mergeAlts :: [Alt b] -> [Alt b] -> [Alt b]
-- ^ Merge alternatives preserving order; alternatives in
-- the first argument shadow ones in the second
mergeAlts [] as2 = as2
mergeAlts as1 [] = as1
mergeAlts (a1:as1) (a2:as2)
  = case a1 `cmpAlt` a2 of
        LT -> a1 : mergeAlts as1      (a2:as2)
        EQ -> a1 : mergeAlts as1      as2       -- Discard a2
        GT -> a2 : mergeAlts (a1:as1) as2


---------------------------------
trimConArgs :: AltCon -> [SeqCoreArg] -> [SeqCoreArg]
-- ^ Given:
--
-- > case (C a b x y) of
-- >        C b x y -> ...
--
-- We want to drop the leading type argument of the scrutinee
-- leaving the arguments to match agains the pattern

trimConArgs DEFAULT      args = assert( null args ) []
trimConArgs (LitAlt _)   args = assert( null args ) []
trimConArgs (DataAlt dc) args = dropList (dataConUnivTyVars dc) args

filterAlts :: [Unique]             -- ^ Supply of uniques used in case we have to manufacture a new AltCon
           -> Type                 -- ^ Type of scrutinee (used to prune possibilities)
           -> [AltCon]             -- ^ 'imposs_cons': constructors known to be impossible due to the form of the scrutinee
           -> [SeqCoreAlt]         -- ^ Alternatives
           -> ([AltCon], Bool, [SeqCoreAlt])
             -- Returns:
             --  1. Constructors that will never be encountered by the 
             --     *default* case (if any).  A superset of imposs_cons
             --  2. Whether we managed to refine the default alternative into a specific constructor (for statistics only)
             --  3. The new alternatives, trimmed by
             --        a) remove imposs_cons
             --        b) remove constructors which can't match because of GADTs
             --      and with the DEFAULT expanded to a DataAlt if there is exactly
             --      remaining constructor that can match
             --
             -- NB: the final list of alternatives may be empty:
             -- This is a tricky corner case.  If the data type has no constructors,
             -- which GHC allows, or if the imposs_cons covers all constructors (after taking 
             -- account of GADTs), then no alternatives can match.
             --
             -- If callers need to preserve the invariant that there is always at least one branch
             -- in a "case" statement then they will need to manually add a dummy case branch that just
             -- calls "error" or similar.
filterAlts us ty imposs_cons alts 
  | Just (tycon, inst_tys) <- splitTyConApp_maybe ty
  = filter_alts tycon inst_tys
  | otherwise
  = (imposs_cons, False, alts)
  where
    (alts_wo_default, maybe_deflt) = findDefault alts
    alt_cons = [con | Alt con _ _ <- alts_wo_default]

    filter_alts tycon inst_tys 
      = (imposs_deflt_cons, refined_deflt, merged_alts)
     where
       trimmed_alts = filterOut (impossible_alt inst_tys) alts_wo_default

       imposs_deflt_cons = nub (imposs_cons ++ alt_cons)
         -- "imposs_deflt_cons" are handled 
         --   EITHER by the context, 
         --   OR by a non-DEFAULT branch in this case expression.

       merged_alts  = mergeAlts trimmed_alts (maybeToList maybe_deflt')
         -- We need the mergeAlts in case the new default_alt 
         -- has turned into a constructor alternative.
         -- The merge keeps the inner DEFAULT at the front, if there is one
         -- and interleaves the alternatives in the right order

       (refined_deflt, maybe_deflt') = case maybe_deflt of
          Nothing -> (False, Nothing)
          Just deflt_rhs 
             | isAlgTyCon tycon            -- It's a data type, tuple, or unboxed tuples.  
             , not (isNewTyCon tycon)      -- We can have a newtype, if we are just doing an eval:
                                           --      case x of { DEFAULT -> e }
                                           -- and we don't want to fill in a default for them!
             , Just all_cons <- tyConDataCons_maybe tycon
             , let imposs_data_cons = [con | DataAlt con <- imposs_deflt_cons]   -- We now know it's a data type 
                   impossible con   = con `elem` imposs_data_cons || dataConCannotMatch inst_tys con
             -> case filterOut impossible all_cons of
                  -- Eliminate the default alternative
                  -- altogether if it can't match:
                  []    -> (False, Nothing)
                  -- It matches exactly one constructor, so fill it in:
                  [con] -> (True, Just (Alt (DataAlt con) (ex_tvs ++ arg_ids) deflt_rhs))
                    where (ex_tvs, arg_ids) = dataConRepInstPat us con inst_tys
                  _     -> (False, Just (Alt DEFAULT [] deflt_rhs))

             | debugIsOn, isAlgTyCon tycon
             , null (tyConDataCons tycon)
             , not (isFamilyTyCon tycon || isAbstractTyCon tycon)
                   -- Check for no data constructors
                   -- This can legitimately happen for abstract types and type families,
                   -- so don't report that
             -> pprTrace "prepareDefault" (ppr tycon)
                (False, Just (Alt DEFAULT [] deflt_rhs))

             | otherwise -> (False, Just (Alt DEFAULT [] deflt_rhs))

    impossible_alt :: [Type] -> Alt a -> Bool
    impossible_alt _ (Alt con _ _) | con `elem` imposs_cons = True
    impossible_alt inst_tys (Alt (DataAlt con) _ _) = dataConCannotMatch inst_tys con
    impossible_alt _  _                         = False

----------
-- Size --
----------

seqCoreBindsSize :: SeqCoreProgram -> Int
seqCoreBindsSize = sum . map sizeB
  where
    sizeB (NonRec pair) = sizeBP pair
    sizeB (Rec pairs) = sum (sizeBP <$> pairs)
    
    sizeBP (BindTerm x term) = sizeX x + sizeT term
    sizeBP (BindJoin j join) = sizeX j + sizeJ join
    
    sizeX x | isTyVar x = seqType (tyVarKind x) `seq` 1
            | otherwise = seqType (idType x)       `seq`
                          megaSeqIdInfo (idInfo x) `seq`
                          1
    
    sizeJ (Join xs c) = sum (sizeX <$> xs) + sizeC c
    
    sizeT (Var x) = x `seq` 1
    sizeT (Lit lit) = lit `seq` 1
    sizeT (Type ty) = seqType ty `seq` 1
    sizeT (Coercion co) = seqCo co `seq` 1
    sizeT (Lam x v) = sizeX x + sizeT v
    sizeT (Compute ty c) = seqType ty `seq` sizeC c
    
    sizeK (Kont fs e) = sum (sizeF <$> fs) + sizeE e
    
    sizeF (App arg) = sizeT arg
    sizeF (Cast co) = seqCo co `seq` 1
    sizeF (Tick (ProfNote cc _ _)) = cc `seq` 1
    sizeF (Tick _) = 1
    
    sizeE Return = 1
    sizeE (Case x alts) = sizeX x + sum (sizeA <$> alts)
    
    sizeA (Alt con xs c) = con `seq` sum (sizeX <$> xs) + sizeC c
    
    sizeC (Let b c)     = sizeB b + sizeC c
    sizeC (Jump args j) = j `seq` sum (sizeT <$> args) + 1
    sizeC (Eval v k)    = sizeT v + sizeK k

-------------------
-- Eta-reduction --
-------------------

-- (from CoreUtils)
tryEtaReduce :: [Var] -> SeqCoreTerm -> Maybe SeqCoreTerm
tryEtaReduce bndrs body@(Compute _ (Eval fun (Kont fs Return)))
  | ok_fun fun
  = go bndrs fs (mkReflCo Representational (termType body))
  where
    incoming_arity = count isId bndrs

    go :: [Var]            -- Binders, types [a1,a2,a3]
       -> [SeqCoreFrame]   -- Of type a1 -> a2 -> a3 -> tr
       -> Coercion         -- Of type tr ~ ts
       -> Maybe SeqCoreTerm   -- Of type a1 -> a2 -> a3 -> ts
    -- See Note [Eta reduction with casted arguments]
    -- for why we have an accumulating coercion
    go [] [] co
      | let used_vars = termFreeVars fun `unionVarSet` tyCoVarsOfCo co
      , not (any (`elemVarSet` used_vars) bndrs)
      = Just (mkCast fun co)   -- Check for any of the binders free in the result
                               -- including the accumulated coercion

    go (b : bs) (App arg : fs) co
      | Just co' <- ok_arg b arg co
      = go bs fs co'
    
    go bs (Cast co' : fs) co
      = go bs fs (mkTransCo co' co)

    go _ _ _  = Nothing         -- Failure!

    ---------------
    -- Note [Eta reduction conditions]
    ok_fun (Var fun_id)        = ok_fun_id fun_id || all ok_lam bndrs
    ok_fun _fun                = False

    ---------------
    ok_fun_id fun = fun_arity fun >= incoming_arity

    ---------------
    fun_arity fun             -- See Note [Arity care]
       | isLocalId fun
       , isStrongLoopBreaker (idOccInfo fun) = 0
       | arity > 0                           = arity
       | isEvaldUnfolding (idUnfolding fun)  = 1  
            -- See Note [Eta reduction of an eval'd function]
       | otherwise                           = 0
       where
         arity = idArity fun

    ---------------
    ok_lam v = isTyVar v || isEvVar v

    ---------------
    ok_arg :: Var              -- Of type bndr_t
           -> SeqCoreArg       -- Of type arg_t
           -> Coercion         -- Of kind (t1~t2)
           -> Maybe Coercion   -- Of type (arg_t -> t1 ~  bndr_t -> t2)
                               --   (and similarly for tyvars, coercion args)
    -- See Note [Eta reduction with casted arguments]
    ok_arg bndr (Type ty) co
       | Just tv <- getTyVar_maybe ty
       , bndr == tv  = Just (mkForAllCo tv co)
    ok_arg bndr (Var v) co
       | bndr == v   = Just (mkFunCo Representational
                                     (mkReflCo Representational (idType bndr)) co)
    ok_arg bndr (Compute _ (Eval (Var v) (Kont [Cast co_arg] Return))) co
       | bndr == v  = Just (mkFunCo Representational (mkSymCo co_arg) co)
       -- The simplifier combines multiple casts into one,
       -- so we can have a simple-minded pattern match here
    ok_arg _ _ _ = Nothing
tryEtaReduce _ _ = Nothing

termFreeVars :: SeqCoreTerm -> VarSet
-- Cheat for now
termFreeVars = exprFreeVars . termToCoreExpr
