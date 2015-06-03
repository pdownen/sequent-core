module Language.SequentCore.Lint ( lintCoreBindings, lintValue ) where

import Language.SequentCore.Syntax

import Coercion     ( coercionKind, coercionType )
import DataCon
import Id
import Kind
import Literal
import Outputable
import Pair
import Type
import VarEnv

import Control.Monad

type LintM = Either SDoc
type LintEnv = TvSubst

eitherToMaybe :: Either a b -> Maybe a
eitherToMaybe (Left a)  = Just a
eitherToMaybe (Right _) = Nothing

lintCoreBindings :: [SeqCoreBind] -> Maybe SDoc
lintCoreBindings binds = eitherToMaybe $ foldM lintCoreBind emptyTvSubst binds

lintValue :: TvSubst -> SeqCoreValue -> Maybe SDoc
lintValue env val = eitherToMaybe $ lintCoreValue env val 

lintCoreBind :: LintEnv -> SeqCoreBind -> LintM LintEnv
lintCoreBind env (NonRec bndr rhs)
  = do
    let bndrTy = substTy env (idType bndr)
        bndr'  = bndr `setIdType` bndrTy
        env'   = extendTvInScope env bndr'
    case rhs of
      Cont cont -> do
                   contTy <- contIdTyOrError env bndr
                   lintCoreCont (text "in RHS for cont id" <+> ppr bndr)
                                env' contTy cont
      _         -> do
                   rhsTy <- lintCoreValue env' rhs
                   checkRhsType bndr bndrTy rhsTy
    return env'
lintCoreBind env (Rec pairs)
  = do
    let bndrs   = map fst pairs
        bndrTys = map (substTy env . idType) bndrs
        bndrs'  = zipWith setIdType bndrs bndrTys
        env'    = extendTvInScopeList env bndrs'
    rhsTys <- mapM (lintCoreValue env' . snd) pairs
    forM_ (zip3 bndrs bndrTys rhsTys) $ \(bndr, bndrTy, rhsTy) ->
      checkRhsType bndr bndrTy rhsTy
    return env'

lintCoreValue :: LintEnv -> SeqCoreValue -> LintM Type
lintCoreValue env (Var x)
  | not (isLocalId x)
  = return (idType x)
  | Just x' <- lookupInScope (getTvInScope env) x
  = if substTy env (idType x) `eqType` idType x'
      then return $ idType x'
      else Left $ text "variable" <+> pprBndr LetBind x <+> text "bound as"
                                  <+> pprBndr LetBind x'
  | otherwise
  = Left $ text "not found in context:" <+> pprBndr LetBind x

lintCoreValue env (Lam xs k comm)
  = do
    let xs'  = map (substTyInId env) xs
        k'   = substTyInId env k
        env' = extendTvInScopeList env (k' : xs')
    lintCoreCommand env' comm
    retTy <- contIdTyOrError env k'
    return $ mkPiTypes xs' retTy

lintCoreValue env (Cons dc args)
  = do
    let (tyVars, monoTy)  = splitForAllTys $ dataConRepType dc
        (argTys, resTy)   = splitFunTys monoTy
        (tyArgs, valArgs) = partitionTypes args
    unless (length valArgs == dataConRepArity dc) $
      Left (text "wrong number of args for" <+> ppr dc $$ ppr args)
    unless (length tyVars == length tyArgs) $
      Left (text "wrong number of type args for" <+> ppr dc $$ ppr args)
    let augment env' (tyVar, ty)
          = do
            let tyVarTy = substTy env' (idType tyVar)
                kind    = substTy env' (typeKind ty)
            unless (tyVarTy `eqType` kind) $
              mkError (text "kind of arg" <+> ppr ty <+> text "for" <+> ppr tyVar)
                (ppr tyVarTy) (ppr kind)
            let tyVar' = tyVar `setIdType` tyVarTy
                ty'    = substTy env' ty
            return $ extendTvSubst env' tyVar' ty' `extendTvInScope` tyVar'
    env' <- foldM augment env (zip tyVars tyArgs)
    let doArg argTy arg
          = do
            let argTy' = substTy env' argTy
            checkingType (ppr arg) argTy' $ lintCoreValue env' arg
    zipWithM_ doArg argTys valArgs
    return $ substTy env' resTy

lintCoreValue env (Compute bndr comm)
  = do
    ty <- contIdTyOrError env bndr
    lintCoreCommand env' comm
    return ty
  where
    env' = extendTvInScopeSubsted env bndr

lintCoreValue _env (Lit lit)
  = return $ literalType lit

lintCoreValue env (Type ty)
  = return $ typeKind (substTy env ty)

lintCoreValue env (Coercion co)
  = return $ substTy env (coercionType co)

lintCoreValue _env (Cont cont)
  = Left $ text "unexpected continuation as value:" <+> ppr cont

lintCoreCommand :: LintEnv -> SeqCoreCommand -> LintM ()
lintCoreCommand env (Command { cmdLet = binds, cmdValue = val, cmdCont = cont })
  = do
    env' <- foldM lintCoreBind env binds
    lintCoreCut env' val cont

lintCoreCut :: LintEnv -> SeqCoreValue -> SeqCoreCont -> LintM ()
lintCoreCut env val cont
  = do
    ty <- lintCoreValue env val
    lintCoreCont (text "in continuation of" <+> ppr val) env ty cont

lintCoreCont :: SDoc -> LintEnv -> Type -> SeqCoreCont -> LintM ()
lintCoreCont desc env ty (Return k)
  | Just k' <- lookupInScope (getTvInScope env) k
  = if substTy env (idType k) `eqType` idType k'
      then void $ checkingType (desc <> colon <+> text "cont variable" <+> ppr k) ty $ contIdTyOrError env k
      else Left $ desc <> colon <+> text "cont variable" <+> pprBndr LetBind k <+> text "bound as"
                                                         <+> pprBndr LetBind k'
  | otherwise
  = Left $ text "not found in context:" <+> pprBndr LetBind k
lintCoreCont desc env ty (App (Type tyArg) cont)
  | Just (tyVar, resTy) <- splitForAllTy_maybe (substTy env ty)
  = do
    let tyArg' = substTy env tyArg
    if typeKind tyArg' `isSubKind` idType tyVar
      then do
           let env' = extendTvSubst env tyVar tyArg'
               -- Don't reapply the rest of the substitution; just apply the new thing
               resTy' = substTy (extendTvSubst emptyTvSubst tyVar tyArg') resTy
           lintCoreCont desc env' resTy' cont
      else mkError (desc <> colon <+> text "type argument" <+> ppr tyArg)
             (ppr (typeKind tyArg')) (ppr (idType tyVar))
  | otherwise
  = Left $ desc <> colon <+> text "not a forall type:" <+> ppr ty
lintCoreCont desc env ty (App arg cont)
  | Just (argTy, resTy) <- splitFunTy_maybe (substTy env ty)
  = do
    void $ checkingType (desc <> colon <+> ppr arg) argTy $ lintCoreValue env arg
    lintCoreCont desc env resTy cont
  | otherwise
  = Left $ desc <> colon <+> text "not a function type:" <+> ppr ty
lintCoreCont desc env ty (Cast co cont)
  = do
    let Pair fromTy toTy = coercionKind co
        fromTy' = substTy env fromTy
        toTy'   = substTy env toTy
    void $ checkingType (desc <> colon <+> text "incoming type of" <+> ppr co) ty $ return fromTy'
    lintCoreCont desc env toTy' cont
lintCoreCont desc env ty (Tick _ cont)
  = lintCoreCont desc env ty cont
lintCoreCont desc env ty (Case bndr alts)
  = do
    let env' = extendTvInScopeSubsted env bndr
    forM_ alts $ \(Alt _ bndrs rhs) ->
      lintCoreCommand (extendTvInScopeListSubsted env' bndrs) rhs
    void $ checkingType (desc <> colon <+> text "type of case binder") ty $
      return $ substTy env (idType bndr)

extendTvInScopeSubsted :: TvSubst -> Var -> TvSubst
extendTvInScopeSubsted tvs var
  = extendTvInScope tvs (substTyInId tvs var)

substTyInId :: TvSubst -> Var -> Var
substTyInId tvs var = var `setIdType` substTy tvs (idType var)

extendTvInScopeListSubsted :: TvSubst -> [Var] -> TvSubst
extendTvInScopeListSubsted tvs vars
  = foldr (flip extendTvInScopeSubsted) tvs vars

mkError :: SDoc -> SDoc -> SDoc -> LintM ()
mkError desc ex act = Left (desc $$ text "expected:" <+> ex
                                 $$ text "actual:" <+> act)
  
checkRhsType :: Var -> Type -> Type -> LintM ()
checkRhsType bndr bndrTy rhsTy
  = unless (bndrTy `eqType` rhsTy) $
      mkError (text "type of RHS of" <+> ppr bndr) (ppr bndrTy) (ppr rhsTy)

checkingType :: SDoc -> Type -> LintM Type -> LintM Type
checkingType desc ex go
  = do
    act <- go
    unless (ex `eqType` act) $ mkError desc (ppr ex) (ppr act)
    return act

{-
checkingPiVsSigmaType :: SDoc -> Type -> LintM Type -> LintM Type
checkingPiVsSigmaType desc ex go
  = do
    act <- go
    unless (ex `orthTypes` act) $
      Left (desc $$ text "expected orth to:" <+> pprSigmaTy ex
                 $$ text "          actual:" <+> pprSigmaTy act)
    return act
-}
  
contIdTyOrError :: LintEnv -> ContId -> LintM Type
contIdTyOrError env k
  = case splitFunTy_maybe (substTy env (idType k)) of
      Just (arg, _) -> return arg
      _             -> Left (text "bad cont type:" <+> pprBndr LetBind k)

{-
promotedPairDataCon :: TyCon
promotedPairDataCon = promotedTupleDataCon BoxedTuple 2

-- Dual of a pi-type. We fake this using promoted pairs. Can't be confused with
-- the type of actual data, since such a thing always has kind * (or # or a few
-- others, but certainly not kind '(*, *)).
mkSigmaType :: Type -> Type -> Type
mkSigmaType ty1 ty2 = mkTyConApp promotedPairDataCon [ty1, ty2]

splitSigmaTy_maybe :: Type -> Maybe (Type, Type)
splitSigmaTy_maybe ty
  | Just (con, [t1, t2]) <- splitTyConApp_maybe ty
  , con == promotedPairDataCon
  = Just (t1, t2)
  | otherwise
  = Nothing

orthTypes :: Type -> Type -> Bool
orthTypes ty1 ty2
  | Just (tyArg, restTy2) <- splitSigmaTy_maybe ty2
  = case splitForAllTy_maybe ty1 of
      Nothing -> False
      Just (tyVar, restTy1)
        -> let boundTy | isKindVar tyVar = typeKind tyArg -- undo sigma-type hack
                       | otherwise       = tyArg
               tvs = extendTvSubst emptyTvSubst tyVar boundTy
           in substTy tvs restTy1 `orthTypes` substTy tvs restTy2
           -- It's O(n^2) to substitute one-by-one, but types aren't that big
  | otherwise
  = ty1 `eqType` ty2

pprSigmaTy :: Type -> SDoc
pprSigmaTy ty
  | Just (ty1, ty2) <- splitSigmaTy_maybe ty
  = parens (ppr ty1 <> comma <+> pprSigmaTy ty2)
  | otherwise
  = ppr ty
-}