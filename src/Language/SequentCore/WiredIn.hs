module Language.SequentCore.WiredIn (
  kontKindTyCon, kontTyCon,
  
  mkKontKind, mkKontTy, isKontTy, isKontTy_maybe,
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

sequentCoreTag, sequentCoreWiredInTag :: Char
-- Must be different from any other unique tag!! See the Unique module
sequentCoreTag        = 'Q'
sequentCoreWiredInTag = 'q'

kontKindKey, kontTypeKey,
  lamKontKey, argKontKey, letKontKey, caseKontKey, kontArgKey :: Unique
kontKindKey: kontTypeKey:
  lamKontKey: argKontKey: letKontKey: caseKontKey: kontArgKey: _
  = map (mkUnique sequentCoreWiredInTag) [1..]

lamKontName, argKontName, letKontName, caseKontName, kontArgName :: Name
[lamKontName, argKontName, letKontName, caseKontName, kontArgName] =
  zipWith mkSystemVarName
    [lamKontKey,    argKontKey,    letKontKey,    caseKontKey,    kontArgKey]
    [fsLit "*lamk", fsLit "*argk", fsLit "*letk", fsLit "*casek", fsLit "karg"]

kontKindTyConName, kontTyConName :: Name
kontKindTyConName = mkPrimTyConName (fsLit "ContKind") kontKindKey    kontKindTyCon
kontTyConName     = mkPrimTyConName (fsLit "Cont#")    kontTypeKey    kontTyCon

mkLamKontId, mkArgKontId, mkLetKontId, mkCaseKontId :: Type -> Var
[mkLamKontId, mkArgKontId, mkLetKontId, mkCaseKontId]
  = map (\name ty -> mkLocalId name (mkKontTy ty))
      [lamKontName, argKontName, letKontName, caseKontName]

mkKontArgId :: Type -> Id
mkKontArgId ty = mkLocalId kontArgName ty

kontKindTyCon, kontTyCon :: TyCon
kontKindTyCon = mkKindTyCon kontKindTyConName superKind

-- TODO VoidRep isn't really right, but does it matter? This type should never
-- appear in Core anyway.
kontTyCon = mkPrimTyCon kontTyConName kind [Representational] VoidRep
  where
    kKi  = mkTyVarTy kKiVar
    kind = mkPiTypes [kKiVar] (mkFunTy kKi (mkKontKind kKi))

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
