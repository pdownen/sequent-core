module Language.SequentCore.WiredIn (
  kontKindTyCon, kontArgsKindTyCon, kontTyCon, kontArgsTyCon, ubxExistsTyCon,
  
  mkKontKind, kontArgsKind, mkKontTy, mkKontArgsTy, mkUbxExistsTy,
  isKontKind, isKontKind_maybe, isKontArgsKind,
  isKontTy, isKontTy_maybe, isKontArgsTy, isKontArgsTy_maybe,
  isUbxExistsTy, isUbxExistsTy_maybe,
  applyUbxExists, applyUbxExists_maybe, applysUbxExists_maybe,
  
  sequentCoreTag, sequentCoreWiredInTag,
  
  mkLamKontId, mkLetKontId, mkArgKontId, mkCaseKontId, mkKontArgId
) where

import FastString
import Id
import Kind
import Maybes
import Name
import Outputable
import PrelNames
import TyCon
import Type
import TysPrim
import Unique

import Control.Monad

sequentCoreTag, sequentCoreWiredInTag :: Char
-- Must be different from any other unique tag!! See the Unique module
sequentCoreTag        = 'Q'
sequentCoreWiredInTag = 'q'

kontKindKey, kontArgsKindKey, kontTypeKey, kontArgsTypeKey, ubxExistsTypeKey,
  lamKontKey, argKontKey, letKontKey, kontArgKey, caseKontKey :: Unique
kontKindKey: kontArgsKindKey: kontTypeKey: kontArgsTypeKey: ubxExistsTypeKey:
  lamKontKey: argKontKey: letKontKey: kontArgKey: caseKontKey: _
  = map (mkUnique sequentCoreWiredInTag) [1..]

lamKontName, argKontName, letKontName, caseKontName, kontArgName :: Name
[lamKontName, argKontName, letKontName, caseKontName, kontArgName] =
  zipWith mkSystemVarName
    [lamKontKey,    argKontKey,    letKontKey,    caseKontKey,    kontArgKey]
    [fsLit "*lamk", fsLit "*argk", fsLit "*letk", fsLit "*casek", fsLit "karg"]

kontKindTyConName, kontArgsKindTyConName, kontTyConName, kontArgsTyConName, ubxExistsTyConName :: Name
kontKindTyConName     = mkPrimTyConName (fsLit "ContKind")     kontKindKey      kontKindTyCon
kontArgsKindTyConName = mkPrimTyConName (fsLit "ContArgsKind") kontArgsKindKey  kontArgsKindTyCon
kontTyConName         = mkPrimTyConName (fsLit "Cont#")        kontTypeKey      kontTyCon
kontArgsTyConName     = mkPrimTyConName (fsLit "ContArgs#")    kontArgsTypeKey  kontArgsTyCon
ubxExistsTyConName    = mkPrimTyConName (fsLit "Exists#")      ubxExistsTypeKey ubxExistsTyCon

mkLamKontId, mkArgKontId, mkLetKontId, mkCaseKontId :: Type -> Var
[mkLamKontId, mkArgKontId, mkLetKontId, mkCaseKontId]
  = map (\name ty -> mkLocalId name (mkKontTy ty))
      [lamKontName, argKontName, letKontName, caseKontName]

mkKontArgId :: Type -> Id
mkKontArgId ty = mkLocalId kontArgName ty

kontKindTyCon, kontTyCon, ubxExistsTyCon, kontArgsKindTyCon, kontArgsTyCon :: TyCon
kontKindTyCon = mkKindTyCon kontKindTyConName (superKind `mkArrowKind` superKind)

-- TODO VoidRep isn't really right, but does it matter? This type should never
-- appear in Core anyway.
kontTyCon = mkPrimTyCon kontTyConName kind roles VoidRep
  where
    kKi   = mkTyVarTy kKiVar
    kind  = mkPiTypes [kKiVar] (mkFunTy kKi (mkKontKind kKi))
    roles = [Representational, Representational]

kontArgsKindTyCon = mkKindTyCon kontArgsKindTyConName superKind

kontArgsTyCon = mkPrimTyCon kontArgsTyConName kind [Representational] VoidRep
  where
    kind  = unliftedTypeKind `mkArrowKind` kontArgsKind

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

kontArgsKind :: Kind
kontArgsKind = mkTyConTy kontArgsKindTyCon

mkKontArgsTy :: Type -> Type
mkKontArgsTy ty = mkTyConApp kontArgsTyCon [ty]

isKontKind, isKontArgsKind :: Kind -> Bool
isKontKind = isJust . isKontKind_maybe

isKontArgsKind ki | Just [] <- matchTyConApp ki kontArgsTyCon
                  = True
isKontArgsKind _  = False

isKontKind_maybe :: Kind -> Maybe Kind
isKontKind_maybe ki = do [arg] <- matchTyConApp ki kontKindTyCon
                         return arg

isKontTy, isKontArgsTy, isUbxExistsTy :: Type -> Bool
isKontTy      = isJust . isKontTy_maybe
isKontArgsTy  = isJust . isKontArgsTy_maybe
isUbxExistsTy = isJust . isUbxExistsTy_maybe

isKontTy_maybe :: Type -> Maybe Type
isKontTy_maybe ty = do [_, arg] <- matchTyConApp ty kontTyCon
                       return arg

isKontArgsTy_maybe :: Type -> Maybe Type
isKontArgsTy_maybe ty = do [arg] <- matchTyConApp ty kontArgsTyCon
                           return arg

isUbxExistsTy_maybe :: Type -> Maybe (TyVar, Type)
isUbxExistsTy_maybe ty = do [arg] <- matchTyConApp ty ubxExistsTyCon
                            splitForAllTy_maybe arg

applyUbxExists :: Type -> Type -> Type
applyUbxExists ty tyArg
  = applyUbxExists_maybe ty tyArg `orElse` pprPanic "applyUbxExists" (ppr ty <+> ppr tyArg)

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
