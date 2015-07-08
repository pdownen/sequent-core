module Language.SequentCore.WiredIn (
  kontKindTyCon, kontTyCon, kontFunTyCon,
  
  mkKontKind, mkKontTy, isKontTy, isKontTy_maybe,
  mkKontFunTy, isKontFunTy, splitKontFunTy_maybe,
  sequentCoreTag, sequentCoreWiredInTag,
  
  mkLamKontId, mkLetKontId, mkArgKontId, mkCaseKontId, mkKontArgId
) where

import FastString
import Id
import Kind
import Name
import PrelNames
import TyCon
import Type
import TypeRep     ( Type(TyConApp) ) -- for seeing type synonyms
import TysPrim
import Unique

sequentCoreTag, sequentCoreWiredInTag :: Char
-- Must be different from any other unique tag!! See the Unique module
sequentCoreTag        = 'Q'
sequentCoreWiredInTag = 'q'

kontKindKey, kontTypeKey, kontFunTypeKey,
  lamKontKey, argKontKey, letKontKey, caseKontKey, kontArgKey :: Unique
[ kontKindKey, kontTypeKey, kontFunTypeKey,
  lamKontKey, argKontKey, letKontKey, caseKontKey, kontArgKey ]
  = map (mkUnique sequentCoreWiredInTag) [1..8]

lamKontName, argKontName, letKontName, caseKontName, kontArgName :: Name
[lamKontName, argKontName, letKontName, caseKontName, kontArgName] =
  zipWith mkSystemVarName
    [lamKontKey,    argKontKey,    letKontKey,    caseKontKey,    kontArgKey]
    [fsLit "*lamk", fsLit "*argk", fsLit "*letk", fsLit "*casek", fsLit "karg"]

kontKindTyConName, kontTyConName, kontFunTyConName :: Name
kontKindTyConName = mkPrimTyConName (fsLit "ContKind") kontKindKey    kontKindTyCon
kontTyConName     = mkPrimTyConName (fsLit "Cont#")    kontTypeKey    kontTyCon
kontFunTyConName  = mkPrimTyConName (fsLit "KontFun")  kontFunTypeKey kontFunTyCon

mkLamKontId, mkArgKontId, mkLetKontId, mkCaseKontId :: Type -> Var
[mkLamKontId, mkArgKontId, mkLetKontId, mkCaseKontId]
  = map (\name ty -> mkLocalId name (mkKontTy ty))
      [lamKontName, argKontName, letKontName, caseKontName]

mkKontArgId :: Type -> Id
mkKontArgId ty = mkLocalId kontArgName ty

kontKindTyCon, kontTyCon, kontFunTyCon :: TyCon
kontKindTyCon = mkKindTyCon kontKindTyConName superKind

-- TODO VoidRep isn't really right, but does it matter? This type should never
-- appear in Core anyway.
kontTyCon = mkPrimTyCon kontTyConName kind [Representational] VoidRep
  where
    kKi  = mkTyVarTy kKiVar
    kind = mkPiTypes [kKiVar] (mkFunTy kKi (mkKontKind kKi))

kontFunTyCon = mkSynTyCon kontFunTyConName kind vars roles rhs parent
  where
    kind = mkArrowKinds [openTypeKind, openTypeKind] liftedTypeKind
    vars = [openAlphaTyVar, openBetaTyVar]
    roles = [Representational, Representational]
    rhs = SynonymTyCon (mkFunTy openAlphaTy openBetaTy)
    parent = NoParentTyCon

mkKontKind :: Kind -> Kind
mkKontKind kind = mkTyConApp kontKindTyCon [kind]

mkKontTy :: Type -> Type
mkKontTy ty = mkTyConApp kontTyCon [typeKind ty, ty]

isKontTy :: Type -> Bool
isKontTy ty | Just (con, _) <- splitTyConApp_maybe ty
            = con == kontTyCon
            | otherwise
            = False

isKontTy_maybe :: Type -> Maybe Type
isKontTy_maybe ty | Just (con, [_, arg]) <- splitTyConApp_maybe ty
                  , con == kontTyCon
                  = Just arg
                  | otherwise
                  = Nothing

mkKontFunTy :: Type -> Type -> Type
mkKontFunTy inTy outTy = mkTyConApp kontFunTyCon [inTy, outTy]

-- Note that we *don't* use splitTyConApp_maybe here because the whole point is
-- to check for a type synonym ...

isKontFunTy :: Type -> Bool
isKontFunTy (TyConApp con _) = con == kontFunTyCon
isKontFunTy _                = False

splitKontFunTy_maybe :: Type -> Maybe (Type, Type)
splitKontFunTy_maybe (TyConApp con [inTy, outTy]) | con == kontFunTyCon
  = Just (inTy, outTy)
splitKontFunTy_maybe _
  = Nothing