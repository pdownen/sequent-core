module Language.SequentCore.Subst (
  -- * Main data types
        Subst(..), -- Implementation exported for supercompiler's Renaming.hs only
        TvSubstEnv, IdSubstEnv, InScopeSet,

        -- ** Substituting into expressions and related types
        deShadowBinds, substSpec, substRulesForImportedIds,
        substTy, substCo, substTerm, substBind, substBindSC,
        substUnfolding, substUnfoldingSC,
        lookupIdSubst, lookupTvSubst, lookupCvSubst, substIdOcc,
        substTickish, substVarSet,

        -- ** Operations on substitutions
        emptySubst, mkEmptySubst, mkSubst, mkOpenSubst, substInScope, isEmptySubst, 
        extendIdSubst, extendIdSubstList, extendTvSubst, extendTvSubstList,
        extendCvSubst, extendCvSubstList,
        extendSubst, extendSubstList, extendSubstWithVar, zapSubstEnv,
        addInScopeSet, extendInScope, extendInScopeList, extendInScopeIds,
        isInScope, setInScope,
        delBndr, delBndrs,

        -- ** Substituting and cloning binders
        substBndr, substBndrs, substRecBndrs,
        cloneBndr, cloneBndrs, cloneIdBndr, cloneIdBndrs, cloneRecIdBndrs
) where

import Language.SequentCore.Syntax
import {-# SOURCE #-} Language.SequentCore.Translate

{-
 - This is mostly pulled from the CoreSubst code in GHC 7.8. 
 -}
import qualified Type
import qualified Coercion

import Type     hiding ( substTy, extendTvSubst, extendTvSubstList
                       , isInScope, substTyVarBndr, cloneTyVarBndr )
import Coercion hiding ( substTy, substCo, extendTvSubst
                       , substTyVarBndr, substCoVarBndr )
import CoreFVs
import qualified CoreSubst
import CoreSubst       ( simpleOptExprWith )
import CoreSyn         ( Tickish(..), Unfolding(..), CoreRule(..)
                       , seqExpr, isStableSource, isClosedUnfolding )
import FastString
import Id
import IdInfo
import Maybes
import Name
import Outputable
import UniqSupply
import Unique
import Var
import VarEnv
import VarSet

import Control.Exception ( assert )
import Data.List         ( mapAccumL )

-- | A substitution environment, containing both 'Id' and 'TyVar' substitutions.
--
-- Some invariants apply to how you use the substitution:
--
-- 1. #in_scope_invariant# The in-scope set contains at least those 'Id's and 'TyVar's that will be in scope /after/
-- applying the substitution to a term. Precisely, the in-scope set must be a superset of the free vars of the
-- substitution range that might possibly clash with locally-bound variables in the thing being substituted in.
--
-- 2. #apply_once# You may apply the substitution only /once/
--
-- There are various ways of setting up the in-scope set such that the first of these invariants hold:
--
-- * Arrange that the in-scope set really is all the things in scope
--
-- * Arrange that it's the free vars of the range of the substitution
--
-- * Make it empty, if you know that all the free vars of the substitution are fresh, and hence can't possibly clash
data Subst
  = Subst InScopeSet  -- Variables in in scope (both Ids and TyVars) /after/
                      -- applying the substitution
          IdSubstEnv  -- Substitution for Ids
          TvSubstEnv  -- Substitution from TyVars to Types
          CvSubstEnv  -- Substitution from CoVars to Coercions

        -- INVARIANT 1: See #in_scope_invariant#
        -- This is what lets us deal with name capture properly
        -- It's a hard invariant to check...
        --
        -- INVARIANT 2: The substitution is apply-once; see Note [Apply once] with
        --              Types.TvSubstEnv
        --
        -- INVARIANT 3: See Note [Extending the Subst]

{-
Note [Extending the Subst]
~~~~~~~~~~~~~~~~~~~~~~~~~~
For a core Subst, which binds Ids as well, we make a different choice for Ids
than we do for TyVars.  

For TyVars, see Note [Extending the TvSubst] with Type.TvSubstEnv

For Ids, we have a different invariant
        The IdSubstEnv is extended *only* when the Unique on an Id changes
        Otherwise, we just extend the InScopeSet

In consequence:

* If the TvSubstEnv and IdSubstEnv are both empty, substTerm would be a
  no-op, so substTermSC ("short cut") does nothing.

  However, substTerm still goes ahead and substitutes.  Reason: we may
  want to replace existing Ids with new ones from the in-scope set, to
  avoid space leaks.

* In substIdBndr, we extend the IdSubstEnv only when the unique changes

* If the CvSubstEnv, TvSubstEnv and IdSubstEnv are all empty,
  substTerm does nothing (Note that the above rule for substIdBndr
  maintains this property.  If the incoming envts are both empty, then
  substituting the type and IdInfo can't change anything.)

* In lookupIdSubst, we *must* look up the Id in the in-scope set, because
  it may contain non-trivial changes.  Example:
        (/\a. \x:a. ...x...) Int
  We extend the TvSubstEnv with [a |-> Int]; but x's unique does not change
  so we only extend the in-scope set.  Then we must look up in the in-scope
  set when we find the occurrence of x.

* The requirement to look up the Id in the in-scope set means that we
  must NOT take no-op short cut when the IdSubst is empty.
  We must still look up every Id in the in-scope set.

* (However, we don't need to do so for expressions found in the IdSubst
  itself, whose range is assumed to be correct wrt the in-scope set.)

Why do we make a different choice for the IdSubstEnv than the
TvSubstEnv and CvSubstEnv?

* For Ids, we change the IdInfo all the time (e.g. deleting the
  unfolding), and adding it back later, so using the TyVar convention
  would entail extending the substitution almost all the time

* The simplifier wants to look up in the in-scope set anyway, in case it 
  can see a better unfolding from an enclosing case expression

* For TyVars, only coercion variables can possibly change, and they are 
  easy to spot
-}

-- | An environment for substituting for 'Id's
type IdSubstEnv = IdEnv SeqCoreTerm

----------------------------
isEmptySubst :: Subst -> Bool
isEmptySubst (Subst _ id_env tv_env cv_env) 
  = isEmptyVarEnv id_env && isEmptyVarEnv tv_env && isEmptyVarEnv cv_env

emptySubst :: Subst
emptySubst = Subst emptyInScopeSet emptyVarEnv emptyVarEnv emptyVarEnv

mkEmptySubst :: InScopeSet -> Subst
mkEmptySubst in_scope = Subst in_scope emptyVarEnv emptyVarEnv emptyVarEnv

mkSubst :: InScopeSet -> TvSubstEnv -> CvSubstEnv -> IdSubstEnv -> Subst
mkSubst in_scope tvs cvs ids = Subst in_scope ids tvs cvs

-- | Find the in-scope set: see "CoreSubst#in_scope_invariant"
substInScope :: Subst -> InScopeSet
substInScope (Subst in_scope _ _ _) = in_scope

-- | Remove all substitutions for 'Id's and 'Var's that might have been built up
-- while preserving the in-scope set
zapSubstEnv :: Subst -> Subst
zapSubstEnv (Subst in_scope _ _ _) = Subst in_scope emptyVarEnv emptyVarEnv emptyVarEnv

-- | Add a substitution for an 'Id' to the 'Subst': you must ensure that the in-scope set is
-- such that the "CoreSubst#in_scope_invariant" is true after extending the substitution like this
extendIdSubst :: Subst -> Id -> SeqCoreTerm -> Subst
-- ToDo: add an ASSERT that fvs(subst-result) is already in the in-scope set
extendIdSubst (Subst in_scope ids tvs cvs) v r = Subst in_scope (extendVarEnv ids v r) tvs cvs

-- | Adds multiple 'Id' substitutions to the 'Subst': see also 'extendIdSubst'
extendIdSubstList :: Subst -> [(Id, SeqCoreTerm)] -> Subst
extendIdSubstList (Subst in_scope ids tvs cvs) prs = Subst in_scope (extendVarEnvList ids prs) tvs cvs

-- | Add a substitution for a 'TyVar' to the 'Subst': you must ensure that the in-scope set is
-- such that the "CoreSubst#in_scope_invariant" is true after extending the substitution like this
extendTvSubst :: Subst -> TyVar -> Type -> Subst
extendTvSubst (Subst in_scope ids tvs cvs) v r = Subst in_scope ids (extendVarEnv tvs v r) cvs

-- | Adds multiple 'TyVar' substitutions to the 'Subst': see also 'extendTvSubst'
extendTvSubstList :: Subst -> [(TyVar,Type)] -> Subst
extendTvSubstList (Subst in_scope ids tvs cvs) prs = Subst in_scope ids (extendVarEnvList tvs prs) cvs

-- | Add a substitution from a 'CoVar' to a 'Coercion' to the 'Subst': you must ensure that the in-scope set is
-- such that the "CoreSubst#in_scope_invariant" is true after extending the substitution like this
extendCvSubst :: Subst -> CoVar -> Coercion -> Subst
extendCvSubst (Subst in_scope ids tvs cvs) v r = Subst in_scope ids tvs (extendVarEnv cvs v r)

-- | Adds multiple 'CoVar' -> 'Coercion' substitutions to the
-- 'Subst': see also 'extendCvSubst'
extendCvSubstList :: Subst -> [(CoVar,Coercion)] -> Subst
extendCvSubstList (Subst in_scope ids tvs cvs) prs = Subst in_scope ids tvs (extendVarEnvList cvs prs)

-- | Add a substitution appropriate to the thing being substituted
--   (whether an expression, type, or coercion). See also
--   'extendIdSubst', 'extendTvSubst', and 'extendCvSubst'.
extendSubst :: Subst -> Var -> SeqCoreTerm -> Subst
extendSubst subst var arg
  = case arg of
      Type ty     -> assert (isTyVar var) $ extendTvSubst subst var ty
      Coercion co -> assert (isCoVar var) $ extendCvSubst subst var co
      _           -> assert (isId    var) $ extendIdSubst subst var arg

extendSubstWithVar :: Subst -> Var -> Var -> Subst
extendSubstWithVar subst v1 v2
  | isTyVar v1 = assert (isTyVar v2) $ extendTvSubst subst v1 (mkTyVarTy v2)
  | isCoVar v1 = assert (isCoVar v2) $ extendCvSubst subst v1 (mkCoVarCo v2)
  | otherwise  = assert (isId    v2) $ extendIdSubst subst v1 (Var v2)

-- | Add a substitution as appropriate to each of the terms being
--   substituted (whether expressions, types, or coercions). See also
--   'extendSubst'.
extendSubstList :: Subst -> [(Var,SeqCoreTerm)] -> Subst
extendSubstList subst []              = subst
extendSubstList subst ((var,rhs):prs) = extendSubstList (extendSubst subst var rhs) prs

-- | Find the substitution for an 'Id' in the 'Subst'
lookupIdSubst :: SDoc -> Subst -> Id -> SeqCoreTerm
lookupIdSubst doc (Subst in_scope ids _ _) v
  | not (isLocalId v) = Var v
  | Just e  <- lookupVarEnv ids       v = e
  | Just v' <- lookupInScope in_scope v = Var v'
        -- Vital! See Note [Extending the Subst]
  | otherwise = pprTrace "Subst.lookupIdSubst" ( doc <+> ppr v 
                            $$ ppr in_scope) 
                Var v

-- | Find the substitution for a 'TyVar' in the 'Subst'
lookupTvSubst :: Subst -> TyVar -> Type
lookupTvSubst (Subst _ _ tvs _) v = assert (isTyVar v) $ lookupVarEnv tvs v `orElse` Type.mkTyVarTy v

-- | Find the coercion substitution for a 'CoVar' in the 'Subst'
lookupCvSubst :: Subst -> CoVar -> Coercion
lookupCvSubst (Subst _ _ _ cvs) v = assert (isCoVar v) $ lookupVarEnv cvs v `orElse` mkCoVarCo v

delBndr :: Subst -> Var -> Subst
delBndr (Subst in_scope ids tvs cvs) v
  | isCoVar v = Subst in_scope ids tvs (delVarEnv cvs v)
  | isTyVar v = Subst in_scope ids (delVarEnv tvs v) cvs
  | otherwise = Subst in_scope (delVarEnv ids v) tvs cvs

delBndrs :: Subst -> [Var] -> Subst
delBndrs (Subst in_scope ids tvs cvs) vs
  = Subst in_scope (delVarEnvList ids vs) (delVarEnvList tvs vs) (delVarEnvList cvs vs)
      -- Easiest thing is just delete all from all!

-- | Simultaneously substitute for a bunch of variables
--   No left-right shadowing
--   ie the substitution for   (\x \y. e) a1 a2
--      so neither x nor y scope over a1 a2
mkOpenSubst :: InScopeSet -> [(Var,SeqCoreTerm)] -> Subst
mkOpenSubst in_scope pairs = Subst in_scope
                                   (mkVarEnv [(id,e)  | (id, e) <- pairs, isId id])
                                   (mkVarEnv [(tv,ty) | (tv, Type ty) <- pairs])
                                   (mkVarEnv [(v,co)  | (v, Coercion co) <- pairs])

------------------------------
isInScope :: Var -> Subst -> Bool
isInScope v (Subst in_scope _ _ _) = v `elemInScopeSet` in_scope

-- | Add the 'Var' to the in-scope set, but do not remove
-- any existing substitutions for it
addInScopeSet :: Subst -> VarSet -> Subst
addInScopeSet (Subst in_scope ids tvs cvs) vs
  = Subst (in_scope `extendInScopeSetSet` vs) ids tvs cvs

-- | Add the 'Var' to the in-scope set: as a side effect,
-- and remove any existing substitutions for it
extendInScope :: Subst -> Var -> Subst
extendInScope (Subst in_scope ids tvs cvs) v
  = Subst (in_scope `extendInScopeSet` v) 
          (ids `delVarEnv` v) (tvs `delVarEnv` v) (cvs `delVarEnv` v)

-- | Add the 'Var's to the in-scope set: see also 'extendInScope'
extendInScopeList :: Subst -> [Var] -> Subst
extendInScopeList (Subst in_scope ids tvs cvs) vs
  = Subst (in_scope `extendInScopeSetList` vs) 
          (ids `delVarEnvList` vs) (tvs `delVarEnvList` vs) (cvs `delVarEnvList` vs)

-- | Optimized version of 'extendInScopeList' that can be used if you are certain 
-- all the things being added are 'Id's and hence none are 'TyVar's or 'CoVar's
extendInScopeIds :: Subst -> [Id] -> Subst
extendInScopeIds (Subst in_scope ids tvs cvs) vs 
  = Subst (in_scope `extendInScopeSetList` vs) 
          (ids `delVarEnvList` vs) tvs cvs

setInScope :: Subst -> InScopeSet -> Subst
setInScope (Subst _ ids tvs cvs) in_scope = Subst in_scope ids tvs cvs

{-
Pretty printing, for debugging only
-}

instance Outputable Subst where
  ppr (Subst in_scope ids tvs cvs) 
        =  ptext (sLit "<InScope =") <+> braces (fsep (map ppr (varEnvElts (getInScopeVars in_scope))))
        $$ ptext (sLit " IdSubst   =") <+> ppr ids
        $$ ptext (sLit " TvSubst   =") <+> ppr tvs
        $$ ptext (sLit " CvSubst   =") <+> ppr cvs   
         <> char '>'

{-
%************************************************************************
%*                                                                      *
        Core compatibility
%*                                                                      *
%************************************************************************
-}

toCoreIdSubstEnv :: IdSubstEnv -> CoreSubst.IdSubstEnv
toCoreIdSubstEnv = mapVarEnv termToCoreExpr

toCoreSubst :: Subst -> CoreSubst.Subst
toCoreSubst (Subst ins ids tvs cvs)
  = CoreSubst.Subst ins (toCoreIdSubstEnv ids) tvs cvs

{-
%************************************************************************
%*                                                                      *
        Substituting expressions
%*                                                                      *
%************************************************************************
-}

substTerm :: SDoc -> Subst -> SeqCoreTerm -> SeqCoreTerm
substTerm _doc subst orig_term = unT $ subst_expr subst (T orig_term)

subst_term :: Subst -> SeqCoreTerm    -> SeqCoreTerm
subst_comm :: Subst -> SeqCoreCommand -> SeqCoreCommand
subst_cont :: Subst -> SeqCoreCont    -> SeqCoreCont
subst_term subst = unT . subst_expr subst . T
subst_comm subst = unC . subst_expr subst . C
subst_cont subst = unK . subst_expr subst . K

subst_expr :: Subst -> SeqCoreExpr   -> SeqCoreExpr
subst_expr subst expr
  = go expr
  where
    go (T term) = T (goT term)
    go (C comm) = C (goC comm)
    go (K cont) = K (goK cont)
  
    goT (Var v)         = lookupIdSubst (text "subst_term") subst v 
    goT (Type ty)       = Type (substTy subst ty)
    goT (Coercion co)   = Coercion (substCo subst co)
    goT (Cont cont)     = Cont (goK cont)
    goT (Lit lit)       = Lit lit
    goT (Compute k comm)= Compute k' (subst_comm subst' comm)
                      where
                        (subst', k')  = substBndr subst k
    goT (Lam x body)    = Lam x' (subst_term subst' body)
                      where
                        (subst', x') = substBndr subst x
    
    goK (App arg cont)  = App (goT arg) (goK cont)
    goK (Tick tickish cont) = Tick (substTickish subst tickish) (goK cont)
    goK (Cast co cont)      = Cast (substCo subst co) (goK cont)
       -- Do not optimise even identity coercions
       -- Reason: substitution applies to the LHS of RULES, and
       --         if you "optimise" an identity coercion, you may
       --         lose a binder. We optimise the LHS of rules at
       --         construction time

    goK (Case bndr alts) = Case bndr' (map (go_alt subst') alts)
                      where
                        (subst', bndr') = substBndr subst bndr
    goK (Return k)       = case lookupIdSubst (text "subst_cont") subst k of
                             Var k'    -> Return k'
                             Cont cont -> cont
                             other     -> pprPanic "subst_expr::goK" (ppr other)

    goC (Command binds term cont) = Command binds' (subst_term subst' term)
                                                  (subst_cont subst' cont)
                      where
                        (subst', binds') = mapAccumL substBind subst binds

    go_alt subst (Alt con bndrs rhs) = (Alt con bndrs' (subst_comm subst' rhs))
                                 where
                                   (subst', bndrs') = substBndrs subst bndrs

-- | Apply a substititon to an entire 'CoreBind', additionally returning an updated 'Subst'
-- that should be used by subsequent substitutons.
substBind, substBindSC :: Subst -> SeqCoreBind -> (Subst, SeqCoreBind)

substBindSC subst bind    -- Short-cut if the substitution is empty
  | not (isEmptySubst subst)
  = substBind subst bind
  | otherwise
  = case bind of
       NonRec bndr rhs -> (subst', NonRec bndr' rhs)
          where
            (subst', bndr') = substBndr subst bndr
       Rec pairs -> (subst', Rec (bndrs' `zip` rhss'))
          where
            (bndrs, rhss)    = unzip pairs
            (subst', bndrs') = substRecBndrs subst bndrs
            rhss' | isEmptySubst subst' = rhss
                  | otherwise           = map (subst_term subst') rhss

substBind subst (NonRec bndr rhs) = (subst', NonRec bndr' (subst_term subst rhs))
                                  where
                                    (subst', bndr') = substBndr subst bndr

substBind subst (Rec pairs) = (subst', Rec (bndrs' `zip` rhss'))
                            where
                                (bndrs, rhss)    = unzip pairs
                                (subst', bndrs') = substRecBndrs subst bndrs
                                rhss' = map (subst_term subst') rhss

-- | De-shadowing the program is sometimes a useful pre-pass. It can be done simply
-- by running over the bindings with an empty substitution, because substitution
-- returns a result that has no-shadowing guaranteed.
--
-- (Actually, within a single /type/ there might still be shadowing, because 
-- 'substTy' is a no-op for the empty substitution, but that's probably OK.)
--
-- [Aug 09] This function is not used in GHC at the moment, but seems so 
--          short and simple that I'm going to leave it here
deShadowBinds :: [SeqCoreBind] -> [SeqCoreBind]
deShadowBinds binds = snd (mapAccumL substBind emptySubst binds)

{-
%************************************************************************
%*                                                                      *
        Substituting binders
%*                                                                      *
%************************************************************************

Remember that substBndr and friends are used when doing expression
substitution only.  Their only business is substitution, so they
preserve all IdInfo (suitably substituted).  For example, we *want* to
preserve occ info in rules.
-}

-- | Substitutes a 'Var' for another one according to the 'Subst' given, returning
-- the result and an updated 'Subst' that should be used by subsequent substitutons.
-- 'IdInfo' is preserved by this process, although it is substituted into appropriately.
substBndr :: Subst -> Var -> (Subst, Var)
substBndr subst bndr
  | isTyVar bndr  = substTyVarBndr subst bndr
  | isCoVar bndr  = substCoVarBndr subst bndr
  | otherwise     = substIdBndr (text "var-bndr") subst subst bndr

-- | Applies 'substBndr' to a number of 'Var's, accumulating a new 'Subst' left-to-right
substBndrs :: Subst -> [Var] -> (Subst, [Var])
substBndrs subst bndrs = mapAccumL substBndr subst bndrs

-- | Substitute in a mutually recursive group of 'Id's
substRecBndrs :: Subst -> [Id] -> (Subst, [Id])
substRecBndrs subst bndrs 
  = (new_subst, new_bndrs)
  where         -- Here's the reason we need to pass rec_subst to subst_id
    (new_subst, new_bndrs) = mapAccumL (substIdBndr (text "rec-bndr") new_subst) subst bndrs


substIdBndr :: SDoc 
            -> Subst            -- ^ Substitution to use for the IdInfo
            -> Subst -> Id      -- ^ Substitition and Id to transform
            -> (Subst, Id)      -- ^ Transformed pair
                                -- NB: unfolding may be zapped

substIdBndr _doc rec_subst subst@(Subst in_scope env tvs cvs) old_id
  = -- pprTrace "substIdBndr" (doc $$ ppr old_id $$ ppr in_scope) $
    (Subst (in_scope `extendInScopeSet` new_id) new_env tvs cvs, new_id)
  where
    id1 = uniqAway in_scope old_id      -- id1 is cloned if necessary
    id2 | no_type_change = id1
        | otherwise      = setIdType id1 (substTy subst old_ty)

    old_ty = idType old_id
    no_type_change = isEmptyVarEnv tvs || 
                     isEmptyVarSet (Type.tyVarsOfType old_ty)

        -- new_id has the right IdInfo
        -- The lazy-set is because we're in a loop here, with 
        -- rec_subst, when dealing with a mutually-recursive group
    new_id = maybeModifyIdInfo mb_new_info id2
    mb_new_info = substIdInfo rec_subst id2 (idInfo id2)
        -- NB: unfolding info may be zapped

        -- Extend the substitution if the unique has changed
        -- See the notes with substTyVarBndr for the delVarEnv
    new_env | no_change = delVarEnv env old_id
            | otherwise = extendVarEnv env old_id (Var new_id)

    no_change = id1 == old_id
        -- See Note [Extending the Subst]
        -- it's /not/ necessary to check mb_new_info and no_type_change

{-
Now a variant that unconditionally allocates a new unique.
It also unconditionally zaps the OccInfo.
-}

-- | Very similar to 'substBndr', but it always allocates a new 'Unique' for
-- each variable in its output.  It substitutes the IdInfo though.
cloneIdBndr :: Subst -> UniqSupply -> Id -> (Subst, Id)
cloneIdBndr subst us old_id
  = clone_id subst subst (old_id, uniqFromSupply us)

-- | Applies 'cloneIdBndr' to a number of 'Id's, accumulating a final
-- substitution from left to right
cloneIdBndrs :: Subst -> UniqSupply -> [Id] -> (Subst, [Id])
cloneIdBndrs subst us ids
  = mapAccumL (clone_id subst) subst (ids `zip` uniqsFromSupply us)

cloneBndrs :: Subst -> UniqSupply -> [Var] -> (Subst, [Var])
-- Works for all kinds of variables (typically case binders)
-- not just Ids
cloneBndrs subst us vs
  = mapAccumL (\subst (v, u) -> cloneBndr subst u v) subst (vs `zip` uniqsFromSupply us)

cloneBndr :: Subst -> Unique -> Var -> (Subst, Var)
cloneBndr subst uniq v
      | isTyVar v = cloneTyVarBndr subst v uniq
      | otherwise = clone_id subst subst (v,uniq)  -- Works for coercion variables too

-- | Clone a mutually recursive group of 'Id's
cloneRecIdBndrs :: Subst -> UniqSupply -> [Id] -> (Subst, [Id])
cloneRecIdBndrs subst us ids
  = (subst', ids')
  where
    (subst', ids') = mapAccumL (clone_id subst') subst
                               (ids `zip` uniqsFromSupply us)

-- Just like substIdBndr, except that it always makes a new unique
-- It is given the unique to use
clone_id    :: Subst                    -- Substitution for the IdInfo
            -> Subst -> (Id, Unique)    -- Substitition and Id to transform
            -> (Subst, Id)              -- Transformed pair

clone_id rec_subst subst@(Subst in_scope idvs tvs cvs) (old_id, uniq)
  = (Subst (in_scope `extendInScopeSet` new_id) new_idvs tvs new_cvs, new_id)
  where
    id1     = setVarUnique old_id uniq
    id2     = substIdType subst id1
    new_id  = maybeModifyIdInfo (substIdInfo rec_subst id2 (idInfo old_id)) id2
    (new_idvs, new_cvs) | isCoVar old_id = (idvs, extendVarEnv cvs old_id (mkCoVarCo new_id))
                        | otherwise      = (extendVarEnv idvs old_id (Var new_id), cvs)

{-
%************************************************************************
%*                                                                      *
                Types and Coercions
%*                                                                      *
%************************************************************************

For types and coercions we just call the corresponding functions in
Type and Coercion, but we have to repackage the substitution, from a
Subst to a TvSubst.
-}

substTyVarBndr :: Subst -> TyVar -> (Subst, TyVar)
substTyVarBndr (Subst in_scope id_env tv_env cv_env) tv
  = case Type.substTyVarBndr (TvSubst in_scope tv_env) tv of
        (TvSubst in_scope' tv_env', tv') 
           -> (Subst in_scope' id_env tv_env' cv_env, tv')

cloneTyVarBndr :: Subst -> TyVar -> Unique -> (Subst, TyVar)
cloneTyVarBndr (Subst in_scope id_env tv_env cv_env) tv uniq
  = case Type.cloneTyVarBndr (TvSubst in_scope tv_env) tv uniq of
        (TvSubst in_scope' tv_env', tv') 
           -> (Subst in_scope' id_env tv_env' cv_env, tv')

substCoVarBndr :: Subst -> TyVar -> (Subst, TyVar)
substCoVarBndr (Subst in_scope id_env tv_env cv_env) cv
  = case Coercion.substCoVarBndr (CvSubst in_scope tv_env cv_env) cv of
        (CvSubst in_scope' tv_env' cv_env', cv') 
           -> (Subst in_scope' id_env tv_env' cv_env', cv')

-- | See 'Type.substTy'
substTy :: Subst -> Type -> Type 
substTy subst ty = Type.substTy (getTvSubst subst) ty

getTvSubst :: Subst -> TvSubst
getTvSubst (Subst in_scope _ tenv _) = TvSubst in_scope tenv

getCvSubst :: Subst -> CvSubst
getCvSubst (Subst in_scope _ tenv cenv) = CvSubst in_scope tenv cenv

-- | See 'Coercion.substCo'
substCo :: Subst -> Coercion -> Coercion
substCo subst co = Coercion.substCo (getCvSubst subst) co

{-
%************************************************************************
%*                                                                      *
\section{IdInfo substitution}
%*                                                                      *
%************************************************************************
-}

substIdType :: Subst -> Id -> Id
substIdType subst@(Subst _ _ tv_env cv_env) id
  | (isEmptyVarEnv tv_env && isEmptyVarEnv cv_env) || isEmptyVarSet (Type.tyVarsOfType old_ty) = id
  | otherwise   = setIdType id (substTy subst old_ty)
                -- The tyVarsOfType is cheaper than it looks
                -- because we cache the free tyvars of the type
                -- in a Note in the id's type itself
  where
    old_ty = idType id

------------------
-- | Substitute into some 'IdInfo' with regard to the supplied new 'Id'.
substIdInfo :: Subst -> Id -> IdInfo -> Maybe IdInfo
substIdInfo subst new_id info
  | nothing_to_do = Nothing
  | otherwise     = Just (info `setSpecInfo`      substSpec subst new_id old_rules
                               `setUnfoldingInfo` substUnfolding subst old_unf)
  where
    old_rules     = specInfo info
    old_unf       = unfoldingInfo info
    nothing_to_do = isEmptySpecInfo old_rules && isClosedUnfolding old_unf

------------------
-- | Substitutes for the 'Id's within an unfolding
substUnfolding, substUnfoldingSC :: Subst -> Unfolding -> Unfolding
        -- Seq'ing on the returned Unfolding is enough to cause
        -- all the substitutions to happen completely

substUnfoldingSC subst unf       -- Short-cut version
  | isEmptySubst subst = unf
  | otherwise          = substUnfolding subst unf

substUnfolding subst df@(DFunUnfolding { df_bndrs = bndrs, df_args = args })
  = df { df_bndrs = bndrs', df_args = args' }
  where
    (subst',bndrs') = substBndrs subst bndrs
    args'           = map (onCoreExpr (substTerm (text "subst-unf:dfun") subst'))
                        args

substUnfolding subst unf@(CoreUnfolding { uf_tmpl = tmpl, uf_src = src })
        -- Retain an InlineRule!
  | not (isStableSource src)  -- Zap an unstable unfolding, to save substitution work
  = NoUnfolding
  | otherwise                 -- But keep a stable one!
  = seqExpr new_tmpl `seq`
    unf { uf_tmpl = new_tmpl }
  where
    new_tmpl = onCoreExpr (substTerm (text "subst-unf") subst) tmpl

substUnfolding _ unf = unf      -- NoUnfolding, OtherCon

------------------
substIdOcc :: Subst -> Id -> Id
-- These Ids should not be substituted to non-Ids
substIdOcc subst v = case lookupIdSubst (text "substIdOcc") subst v of
                        Var v' -> v'
                        other  -> pprPanic "substIdOcc" (vcat [ppr v <+> ppr other, ppr subst])

------------------
-- | Substitutes for the 'Id's within the 'WorkerInfo' given the new function 'Id'
substSpec :: Subst -> Id -> SpecInfo -> SpecInfo
substSpec subst new_id (SpecInfo rules rhs_fvs)
  = seqSpecInfo new_spec `seq` new_spec
  where
    subst_ru_fn = const (idName new_id)
    new_spec = SpecInfo (map (substRule subst subst_ru_fn) rules)
                        (substVarSet subst rhs_fvs)

------------------
substRulesForImportedIds :: Subst -> [CoreRule] -> [CoreRule]
substRulesForImportedIds subst rules 
  = map (substRule subst not_needed) rules
  where
    not_needed name = pprPanic "substRulesForImportedIds" (ppr name)

------------------
substRule :: Subst -> (Name -> Name) -> CoreRule -> CoreRule

-- The subst_ru_fn argument is applied to substitute the ru_fn field
-- of the rule:
--    - Rules for *imported* Ids never change ru_fn
--    - Rules for *local* Ids are in the IdInfo for that Id,
--      and the ru_fn field is simply replaced by the new name 
--      of the Id
substRule _ _ rule@(BuiltinRule {}) = rule
substRule subst subst_ru_fn rule@(Rule { ru_bndrs = bndrs, ru_args = args
                                       , ru_fn = fn_name, ru_rhs = rhs
                                       , ru_local = is_local })
  = rule { ru_bndrs = bndrs', 
           ru_fn    = if is_local 
                        then subst_ru_fn fn_name 
                        else fn_name,
           ru_args  = map (onCoreExpr (substTerm (text "subst-rule" <+> ppr fn_name) subst')) args,
           ru_rhs   = simpleOptExprWith (toCoreSubst subst') rhs }
           -- Do simple optimisation on RHS, in case substitution lets
           -- you improve it.  The real simplifier never gets to look at it.
  where
    (subst', bndrs') = substBndrs subst bndrs

------------------
substVarSet :: Subst -> VarSet -> VarSet
substVarSet subst fvs
  = foldVarSet (unionVarSet . subst_fv subst) emptyVarSet fvs
  where
    subst_fv subst fv 
        | isId fv   = exprFreeVars (termToCoreExpr (lookupIdSubst (text "substVarSet") subst fv))
        | otherwise = Type.tyVarsOfType (lookupTvSubst subst fv)

------------------
substTickish :: Subst -> Tickish Id -> Tickish Id
substTickish subst (Breakpoint n ids) = Breakpoint n (map do_one ids)
 where do_one x = let (Var x') = lookupIdSubst (text "subst_tickish") subst x in x'
substTickish _subst other = other
