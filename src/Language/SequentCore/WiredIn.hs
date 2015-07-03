module Language.SequentCore.WiredIn (
  contKindTyCon, contTyCon, contFunTyCon,
  
  mkContKind, mkContTy, isContTy, isContTy_maybe,
  mkContFunTy, isContFunTy, splitContFunTy_maybe,
  sequentCoreTag, sequentCoreWiredInTag,
  
  mkLamContId, mkLetContId, mkArgContId, mkCaseContId, mkContArgId
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

contKindKey, contTypeKey, contFunTypeKey,
  lamContKey, argContKey, letContKey, caseContKey, contArgKey :: Unique
[ contKindKey, contTypeKey, contFunTypeKey,
  lamContKey, argContKey, letContKey, caseContKey, contArgKey ]
  = map (mkUnique sequentCoreWiredInTag) [1..8]

lamContName, argContName, letContName, caseContName, contArgName :: Name
[lamContName, argContName, letContName, caseContName, contArgName] =
  zipWith mkSystemVarName
    [lamContKey,    argContKey,    letContKey,    caseContKey,    contArgKey]
    [fsLit "*lamk", fsLit "*argk", fsLit "*letk", fsLit "*casek", fsLit "karg"]

contKindTyConName, contTyConName, contFunTyConName :: Name
contKindTyConName = mkPrimTyConName (fsLit "ContKind") contKindKey    contKindTyCon
contTyConName     = mkPrimTyConName (fsLit "Cont#")    contTypeKey    contTyCon
contFunTyConName  = mkPrimTyConName (fsLit "ContFun")  contFunTypeKey contFunTyCon

mkLamContId, mkArgContId, mkLetContId, mkCaseContId :: Type -> Var
[mkLamContId, mkArgContId, mkLetContId, mkCaseContId]
  = map (\name ty -> mkLocalId name (mkContTy ty))
      [lamContName, argContName, letContName, caseContName]

mkContArgId :: Type -> Id
mkContArgId ty = mkLocalId contArgName ty

contKindTyCon, contTyCon, contFunTyCon :: TyCon
contKindTyCon = mkKindTyCon contKindTyConName superKind

-- TODO VoidRep isn't really right, but does it matter? This type should never
-- appear in Core anyway.
contTyCon = mkPrimTyCon contTyConName kind [Representational] VoidRep
  where
    kKi  = mkTyVarTy kKiVar
    kind = mkPiTypes [kKiVar] (mkFunTy kKi (mkContKind kKi))

contFunTyCon = mkSynTyCon contFunTyConName kind vars roles rhs parent
  where
    kind = mkArrowKinds [openTypeKind, openTypeKind] liftedTypeKind
    vars = [openAlphaTyVar, openBetaTyVar]
    roles = [Representational, Representational]
    rhs = SynonymTyCon (mkFunTy openAlphaTy openBetaTy)
    parent = NoParentTyCon

mkContKind :: Kind -> Kind
mkContKind kind = mkTyConApp contKindTyCon [kind]

mkContTy :: Type -> Type
mkContTy ty = mkTyConApp contTyCon [typeKind ty, ty]

isContTy :: Type -> Bool
isContTy ty | Just (con, _) <- splitTyConApp_maybe ty
            = con == contTyCon
            | otherwise
            = False

isContTy_maybe :: Type -> Maybe Type
isContTy_maybe ty | Just (con, [_, arg]) <- splitTyConApp_maybe ty
                  , con == contTyCon
                  = Just arg
                  | otherwise
                  = Nothing

mkContFunTy :: Type -> Type -> Type
mkContFunTy inTy outTy = mkTyConApp contFunTyCon [inTy, outTy]

-- Note that we *don't* use splitTyConApp_maybe here because the whole point is
-- to check for a type synonym ...

isContFunTy :: Type -> Bool
isContFunTy (TyConApp con _) = con == contFunTyCon
isContFunTy _                = False

splitContFunTy_maybe :: Type -> Maybe (Type, Type)
splitContFunTy_maybe (TyConApp con [inTy, outTy]) | con == contFunTyCon
  = Just (inTy, outTy)
splitContFunTy_maybe _
  = Nothing