module Language.SequentCore.WiredIn (
  kontKindTyCon, kontTyCon, ubxExistsTyCon,
  
  mkKontKind, mkKontTy, mkUbxExistsTy,
  isKontTy, isKontTy_maybe, isUbxExistsTy, isUbxExistsTy_maybe,
  applyUbxExists_maybe, applysUbxExists_maybe,
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
import TysPrim
import Unique

import Control.Monad
import Data.Maybe

sequentCoreTag, sequentCoreWiredInTag :: Char
-- Must be different from any other unique tag!! See the Unique module
sequentCoreTag        = 'Q'
sequentCoreWiredInTag = 'q'

kontKindKey, kontTypeKey, ubxExistsTypeKey,
  lamKontKey, argKontKey, letKontKey, caseKontKey, kontArgKey :: Unique
kontKindKey: kontTypeKey: ubxExistsTypeKey:
  lamKontKey: argKontKey: letKontKey: caseKontKey: kontArgKey: _
  = map (mkUnique sequentCoreWiredInTag) [1..]

lamKontName, argKontName, letKontName, caseKontName, kontArgName :: Name
[lamKontName, argKontName, letKontName, caseKontName, kontArgName] =
  zipWith mkSystemVarName
    [lamKontKey,    argKontKey,    letKontKey,    caseKontKey,    kontArgKey]
    [fsLit "*lamk", fsLit "*argk", fsLit "*letk", fsLit "*casek", fsLit "karg"]

kontKindTyConName, kontTyConName, ubxExistsTyConName :: Name
kontKindTyConName  = mkPrimTyConName (fsLit "ContKind") kontKindKey      kontKindTyCon
kontTyConName      = mkPrimTyConName (fsLit "Cont#")    kontTypeKey      kontTyCon
ubxExistsTyConName = mkPrimTyConName (fsLit "Exists#")  ubxExistsTypeKey ubxExistsTyCon

mkLamKontId, mkArgKontId, mkLetKontId, mkCaseKontId :: Type -> Var
[mkLamKontId, mkArgKontId, mkLetKontId, mkCaseKontId]
  = map (\name ty -> mkLocalId name (mkKontTy ty))
      [lamKontName, argKontName, letKontName, caseKontName]

mkKontArgId :: Type -> Id
mkKontArgId ty = mkLocalId kontArgName ty

kontKindTyCon, kontTyCon, ubxExistsTyCon :: TyCon
kontKindTyCon = mkKindTyCon kontKindTyConName superKind

-- TODO VoidRep isn't really right, but does it matter? This type should never
-- appear in Core anyway.
kontTyCon = mkPrimTyCon kontTyConName kind roles VoidRep
  where
    kKi   = mkTyVarTy kKiVar
    kind  = mkPiTypes [kKiVar] (mkFunTy kKi (mkKontKind kKi))
    roles = [Representational, Representational]

-- TODO We might be able to finagle unboxed existentials by calling mkTupleTyCon
-- with a special DataCon
ubxExistsTyCon = mkPrimTyCon ubxExistsTyConName kind [Representational] VoidRep
  where
    kind  = openTypeKind `mkArrowKind` unliftedTypeKind

mkKontKind :: Kind -> Kind
mkKontKind kind = mkTyConApp kontKindTyCon [kind]

mkKontTy :: Type -> Type
mkKontTy ty = mkTyConApp kontTyCon [typeKind ty, ty]

mkUbxExistsTy :: TyVar -> Type -> Type
mkUbxExistsTy a ty = mkTyConApp ubxExistsTyCon [mkForAllTy a ty]

isKontTy, isUbxExistsTy :: Type -> Bool
isKontTy      = isJust . isKontTy_maybe
isUbxExistsTy = isJust . isUbxExistsTy_maybe

isKontTy_maybe :: Type -> Maybe Type
isKontTy_maybe ty = do [_, arg] <- matchTyConApp ty kontTyCon
                       return arg

isUbxExistsTy_maybe :: Type -> Maybe (TyVar, Type)
isUbxExistsTy_maybe ty = do [arg] <- matchTyConApp ty ubxExistsTyCon
                            splitForAllTy_maybe arg

applyUbxExists_maybe :: Type -> Type -> Maybe Type
applyUbxExists_maybe ty tyArg
  = do
    (a, body) <- isUbxExistsTy_maybe ty
    return $ substTyWith [a] [tyArg] body

applysUbxExists_maybe :: Type -> [Type] -> Maybe Type
applysUbxExists_maybe = foldM applyUbxExists_maybe
  
matchTyConApp :: Type -> TyCon -> Maybe [Type]
matchTyConApp ty con = do (con', args) <- splitTyConApp_maybe ty
                          guard (con == con')
                          return args
