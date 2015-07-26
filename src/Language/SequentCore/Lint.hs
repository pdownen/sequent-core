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
import Data.List

{-
Note [Scope of continuation variables]
--------------------------------------

Terms should always produce a unique result to their given continuation
(i.e. evaluation context). It would be unfortunate if evaluating a term caused
control flow to jump someplace else entirely instead of returning a
result. Maintaining a certain discipline on the scope of continuation variables
prevents unwanted, anamolous jumps of control flow outside of the return path of
a term. More specifically: a term cannot have any reference to a free
continuation variable.

In addition to checking types, we also ensure that terms do not depend on any
continuation variables in their scope. This scoping check is implemented in lint
by maintaining two separate environments: one for continuation variables only,
and another for all other variables. Continuations and commands are type checked
with respect to both environments. When it comes time for checking terms, the
environment of continuation variables is dropped entirely. Going the other way,
checking a compute term introduces a new continuation variable environment for
checking its underlying command, which contains only the continuation
environment introduced by the compute abstraction itself. This restriction means
that every command inside of a compute term *must* exit out of the continuation
it names.
-}

type LintM = Either SDoc
type TermEnv = TvSubst
type KontEnv = TvSubst
type LintEnv = (TermEnv, KontEnv)

termEnv :: LintEnv -> TermEnv
termEnv (env, _enk) = env

kontEnv :: LintEnv -> KontEnv
kontEnv (_env, enk) = enk

mkLintEnv :: TermEnv -> KontEnv -> LintEnv
mkLintEnv env enk = (env, enk)

emptyLintEnv :: LintEnv
emptyLintEnv = mkLintEnv emptyTvSubst emptyTvSubst

extendLintEnv :: LintEnv -> BindPair Var -> LintEnv
extendLintEnv env (BindTerm bndr _term)
  = mapTermLintEnv (\ent -> extendTvInScope ent bndr) env
extendLintEnv env (BindPKont bndr _pk)
  = mapKontLintEnv (\enk -> extendTvInScope enk bndr) env

extendLintEnvList :: LintEnv -> [BindPair Var] -> LintEnv
extendLintEnvList = foldr (flip extendLintEnv)

mapTermLintEnv :: (TermEnv -> TermEnv) -> LintEnv -> LintEnv
mapTermLintEnv f env = mkLintEnv (f (termEnv env)) (kontEnv env)

mapKontLintEnv :: (KontEnv -> KontEnv) -> LintEnv -> LintEnv
mapKontLintEnv f env = mkLintEnv (termEnv env) (f (kontEnv env))

eitherToMaybe :: Either a b -> Maybe a
eitherToMaybe (Left a)  = Just a
eitherToMaybe (Right _) = Nothing

lintCoreBindings :: [SeqCoreBind] -> Maybe SDoc
lintCoreBindings binds = eitherToMaybe $ foldM lintCoreBind emptyLintEnv binds

lintTerm :: TvSubst -> SeqCoreTerm -> Maybe SDoc
lintTerm env term = eitherToMaybe $ lintCoreTerm env term 

lintCoreBind :: LintEnv -> SeqCoreBind -> LintM LintEnv
lintCoreBind env (NonRec pair)
  = do
    let bndr   = binderOfPair pair
        bndrTy = substTy (termEnv env) (idType bndr)
        bndr'  = bndr `setIdType` bndrTy
        pair'  = pair `setPairBinder` bndr'
        env'   = extendLintEnv env pair'
    lintCoreBindPair env pair'
    return env'
lintCoreBind env (Rec pairs)
  = do
    let bndrs   = map binderOfPair pairs
        bndrTys = map (substTy (termEnv env) . idType) bndrs
        bndrs'  = zipWith setIdType bndrs bndrTys
        pairs'  = zipWith setPairBinder pairs bndrs'
        env'    = extendLintEnvList env pairs'
    mapM_ (lintCoreBindPair env') pairs'
    return env'

{-
Note [Checking terms vs. continuations]
---------------------------------------

Checking a term can be done straightforwardly: As usual, we check that it has a
consistent type, and return that type if so. But in the face of polymorphism, we
can't do the same with continuations. Consider:

  $ @ Int; $ 3; $ 4; ret p

What is this continuation's type? Supposing p has type Bool, the most general
type would be forall a. a -> a -> Bool, but it could also be forall a. Int -> a
-> Bool or forall a. Int -> a -> Bool or even conceivably forall a. Int -> Int
-> Bool. Fortunately, we always *expect* a continuation to have a particular
type: If it occurs in a command, it must have the same type as the term, and if
it's bound by a let, it must have the identifier's type.

Hence the asymmetry between lintCoreTerm and lintCoreKont, where the former
returns LintM Type and the latter takes an extra Type parameter but returns
LintM ().
-}

lintCoreBindPair :: LintEnv -> SeqCoreBindPair -> LintM ()
lintCoreBindPair env (BindTerm bndr term)
  = do
    termTy <- lintCoreTerm (termEnv env) term
    checkRhsType bndr (idType bndr) termTy
lintCoreBindPair env (BindPKont bndr (PKont xs comm))
  = do
    lintKontBndrTypes (termEnv env) bndr xs
    let (ent, _) = mapAccumL lintBindInTermEnv (termEnv env) xs
    lintCoreCommand (mkLintEnv ent (kontEnv env)) comm

lintKontBndrTypes :: TermEnv -> SeqCoreBndr -> [SeqCoreBndr] -> LintM ()
lintKontBndrTypes env bndr argBndrs
  = do
    bndrTy <- kontIdTyOrError env bndr
    argsTy <- case isKontArgsTy_maybe bndrTy of
                Just argsTy -> return argsTy
                Nothing     -> Left $ text "binder should have Cont# (ContArgs# _) type:" <+>
                                      pprBndr LetBind bndr
    go argsTy argBndrs
  where
    go ty bndrs
      | isUbxExistsTy ty
      = case bndrs of
          [] -> Left $ text "not enough binders for existential:" <+> pprBndr LetBind bndr
                    $$ text "binders:" <+> sep (map (pprBndr LambdaBind) argBndrs)
          bndr:bndrs' -> go (applyUbxExists ty (substTy env (mkTyVarTy bndr))) bndrs'
      | isUnboxedTupleType ty
      , Just (_, argTys) <- splitTyConApp_maybe ty
      , and $ zipWith eqType argTys (map (substTy env . idType) bndrs)
      = return ()
      | otherwise
      = Left $ text "wrong binder types for continuation binder:" <+> pprBndr LetBind bndr
            $$ text "binders:" <+> sep (map (pprBndr LambdaBind) argBndrs)
            $$ text "as of:" <+> ppr ty $$ text "and:" <+> ppr bndrs

lintCoreTerm :: TermEnv -> SeqCoreTerm -> LintM Type
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
    let (env', x') = lintBindInTermEnv env x
    retTy <- lintCoreTerm env' body
    return $ mkPiType x' retTy

lintCoreTerm env (Compute bndr comm)
  = do
    ty <- kontIdTyOrError env bndr
    lintCoreCommand (mkLintEnv env enk) comm
    return ty
  where
    enk = extendTvInScope emptyTvSubst (substTyInId env bndr)

lintCoreTerm _env (Lit lit)
  = return $ literalType lit

lintCoreTerm env (Type ty)
  = return $ typeKind (substTy env ty)

lintCoreTerm env (Coercion co)
  = return $ substTy env (coercionType co)

lintBindInTermEnv :: TermEnv -> Var -> (TermEnv, Var)
lintBindInTermEnv env x
  | isTyVar x
  = substTyVarBndr env x
  | otherwise
  = (env', x')
  where
    x' = substTyInId env x
    env' = extendTvInScope env x'

lintCoreCommand :: LintEnv -> SeqCoreCommand -> LintM ()
lintCoreCommand env (Let bind comm)
  = do
    env' <- lintCoreBind env bind
    lintCoreCommand env' comm
lintCoreCommand env (Eval term kont)
  = lintCoreCut env term kont
lintCoreCommand env (Jump args j)
  = lintCoreJump env args j

lintCoreCut :: LintEnv -> SeqCoreTerm -> SeqCoreKont -> LintM ()
lintCoreCut env term kont
  = do
    ty <- lintCoreTerm (termEnv env) term
    lintCoreKont (text "in continuation of" <+> ppr term) env ty kont

lintCoreJump :: LintEnv -> [SeqCoreArg] -> PKontId -> LintM ()
lintCoreJump env args j
  = do
    ty <- kontIdTyOrError (termEnv env) j
    argsTy <- case isKontArgsTy_maybe (substTy (termEnv env) ty) of
                Just argsTy -> return argsTy
                Nothing     -> Left $ text "target of jump should have type Cont# (ContArgs# _):" <+>
                                      pprBndr LetBind j
    go args argsTy args
  where
    go (Type argTy : args') ty topArgs
      = case applyUbxExists_maybe ty (substTy (termEnv env) argTy) of
          Just ty' -> go args' ty' topArgs
          Nothing  -> mkError (text "type of polymorphic jump")
                              (text "existential type") (ppr ty)
    go args' ty topArgs
      | isUnboxedTupleType ty
      , Just (_, argTys) <- splitTyConApp_maybe ty
      = forM_ (zip3 [1..] argTys args') $ \(n, argTy, arg) ->
          checkingType (speakNth n <+> text "argument of jump") argTy $
            lintCoreTerm (termEnv env) arg
      | otherwise
      = Left $ text "bad parameterized continuation type in binder:" <+> pprBndr LetBind j
            $$ text "for args:" <+> ppr topArgs

lintCoreKont :: SDoc -> LintEnv -> Type -> SeqCoreKont -> LintM ()
lintCoreKont desc env ty (Return k)
  | Just k' <- lookupInScope (getTvInScope (kontEnv env)) k
  = if substTy (termEnv env) (idType k) `eqType` idType k'
      then void $
           checkingType (desc <> colon <+> text "cont variable" <+> ppr k) ty $
           kontIdTyOrError (termEnv env) k
      else Left $ desc <> colon <+> text "cont variable" <+> pprBndr LetBind k <+> text "bound as"
                                                         <+> pprBndr LetBind k'
  | otherwise
  = Left $ desc <> colon <+> text "not found in context:" <+> pprBndr LetBind k
lintCoreKont desc env ty (App (Type tyArg) kont)
  | Just (tyVar, resTy) <- splitForAllTy_maybe (substTy (termEnv env) ty)
  = do
    let tyArg' = substTy (termEnv env) tyArg
    if typeKind tyArg' `isSubKind` idType tyVar
      then do
           let env' = mapTermLintEnv (\ent -> extendTvSubst ent tyVar tyArg') env
               -- Don't reapply the rest of the substitution; just apply the new thing
               resTy' = substTy (extendTvSubst emptyTvSubst tyVar tyArg') resTy
           lintCoreKont desc env' resTy' kont
      else mkError (desc <> colon <+> text "type argument" <+> ppr tyArg)
             (ppr (typeKind tyArg')) (ppr (idType tyVar))
  | otherwise
  = Left $ desc <> colon <+> text "not a forall type:" <+> ppr ty
lintCoreKont desc env ty (App arg kont)
  | Just (argTy, resTy) <- splitFunTy_maybe (substTy (termEnv env) ty)
  = do
    void $ checkingType (desc <> colon <+> ppr arg) argTy $ lintCoreTerm (termEnv env) arg
    lintCoreKont desc env resTy kont
  | otherwise
  = Left $ desc <> colon <+> text "not a function type:" <+> ppr ty
lintCoreKont desc env ty (Cast co kont)
  = do
    let Pair fromTy toTy = coercionKind co
        fromTy' = substTy (termEnv env) fromTy
        toTy'   = substTy (termEnv env) toTy
    void $ checkingType (desc <> colon <+> text "incoming type of" <+> ppr co) ty $ return fromTy'
    lintCoreKont desc env toTy' kont
lintCoreKont desc env ty (Tick _ kont)
  = lintCoreKont desc env ty kont
lintCoreKont desc env ty (Case bndr alts)
  = do
    let env' = mapTermLintEnv (\ent -> extendTvInScopeSubsted ent bndr) env
    forM_ alts $ \(Alt _ bndrs rhs) ->
      lintCoreCommand (mapTermLintEnv (\ent' -> extendTvInScopeListSubsted ent' bndrs) env') rhs
    void $ checkingType (desc <> colon <+> text "type of case binder") ty $
      return $ substTy (termEnv env) (idType bndr)

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
  = do unless (bndrTy `eqType` rhsTy) $
         mkError (text "type of RHS of" <+> ppr bndr) (ppr bndrTy) (ppr rhsTy)
       let bndrKi = typeKind bndrTy
       unless (isSubOpenTypeKind bndrKi) $
         mkError (text "kind of RHS of" <+> ppr bndr) (ppr openTypeKind) (ppr bndrKi)

checkingType :: SDoc -> Type -> LintM Type -> LintM Type
checkingType desc ex go
  = do
    act <- go
    unless (ex `eqType` act) $ mkError desc (ppr ex) (ppr act)
    return act

kontIdTyOrError :: TermEnv -> KontId -> LintM Type
kontIdTyOrError env k
  = case isKontTy_maybe (substTy env (idType k)) of
      Just arg -> return arg
      _        -> Left (text "bad cont type:" <+> pprBndr LetBind k)
