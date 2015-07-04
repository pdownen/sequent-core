module Language.SequentCore.Lint ( lintCoreBindings, lintTerm ) where

import Language.SequentCore.Syntax
import Language.SequentCore.WiredIn

import Coercion     ( coercionKind, coercionType )
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

lintTerm :: TvSubst -> SeqCoreTerm -> Maybe SDoc
lintTerm env term = eitherToMaybe $ lintCoreTerm env term 

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
                   rhsTy <- lintCoreTerm env' rhs
                   checkRhsType bndr bndrTy rhsTy
    return env'
lintCoreBind env (Rec pairs)
  = do
    let bndrs   = map fst pairs
        bndrTys = map (substTy env . idType) bndrs
        bndrs'  = zipWith setIdType bndrs bndrTys
        env'    = extendTvInScopeList env bndrs'
    rhsTys <- mapM (lintCoreTerm env' . snd) pairs
    forM_ (zip3 bndrs bndrTys rhsTys) $ \(bndr, bndrTy, rhsTy) ->
      checkRhsType bndr bndrTy rhsTy
    return env'

lintCoreTerm :: LintEnv -> SeqCoreTerm -> LintM Type
lintCoreTerm env (Var x)
  | not (isLocalId x)
  = return (idType x)
  | Just x' <- lookupInScope (getTvInScope env) x
  = if substTy env (idType x) `eqType` idType x'
      then return $ idType x'
      else Left $ text "variable" <+> pprBndr LetBind x <+> text "bound as"
                                  <+> pprBndr LetBind x'
  | otherwise
  = Left $ text "not found in context:" <+> pprBndr LetBind x

lintCoreTerm env (Lam x body)
  = do
    let (env', x') = lintBind env x
    retTy <- lintCoreTerm env' body
    return $ mkPiType x' retTy
  where
    lintBind env x
      | isTyVar x
      = substTyVarBndr env x
      | otherwise
      = (env', x')
      where
        x' = substTyInId env x
        env' = extendTvInScope env x'

lintCoreTerm env (Compute bndr comm)
  = do
    ty <- contIdTyOrError env bndr
    lintCoreCommand env' comm
    return ty
  where
    env' = extendTvInScopeSubsted env bndr

lintCoreTerm _env (Lit lit)
  = return $ literalType lit

lintCoreTerm env (Type ty)
  = return $ typeKind (substTy env ty)

lintCoreTerm env (Coercion co)
  = return $ substTy env (coercionType co)

lintCoreTerm _env (Cont cont)
  = Left $ text "unexpected continuation as term:" <+> ppr cont

lintCoreCommand :: LintEnv -> SeqCoreCommand -> LintM ()
lintCoreCommand env (Command { cmdLet = binds, cmdTerm = term, cmdCont = cont })
  = do
    env' <- foldM lintCoreBind env binds
    lintCoreCut env' term cont

lintCoreCut :: LintEnv -> SeqCoreTerm -> SeqCoreCont -> LintM ()
lintCoreCut env term cont
  = do
    ty <- lintCoreTerm env term
    lintCoreCont (text "in continuation of" <+> ppr term) env ty cont

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
    void $ checkingType (desc <> colon <+> ppr arg) argTy $ lintCoreTerm env arg
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

contIdTyOrError :: LintEnv -> ContId -> LintM Type
contIdTyOrError env k
  = case isContTy_maybe (substTy env (idType k)) of
      Just arg -> return arg
      _        -> Left (text "bad cont type:" <+> pprBndr LetBind k)
