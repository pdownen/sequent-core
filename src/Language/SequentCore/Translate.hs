{-# LANGUAGE TupleSections #-}

-- | 
-- Module      : Language.SequentCore.Translate
-- Description : Core \<-\> Sequent Core
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- Translation between Sequent Core and native GHC Core.

module Language.SequentCore.Translate (
  -- $txn
  fromCoreModule, termFromCoreExpr,
  bindsToCore,
  commandToCoreExpr, termToCoreExpr, contToCoreExpr,
  onCoreExpr, onSequentCoreTerm
) where

import Language.SequentCore.Subst
import Language.SequentCore.Syntax
import Language.SequentCore.WiredIn

import qualified CoreSyn as Core
import qualified CoreUtils as Core
import qualified CoreFVs as Core
import Id
import Maybes
import qualified MkCore as Core
import Outputable
import Type        hiding ( substTy )
import VarEnv

import Data.List

-- $txn
-- The translations to and from Sequent Core are /not/ guaranteed to be perfect
-- inverses. However, any differences between @e@ and @commandToCoreExpr
-- (fromCoreExpr e)@ should be operationally insignificant, such as a @let@
-- floating out from a function being applied. A more precise characterization
-- of the indended invariants of these functions would entail some sort of
-- /bisimulation/, but it should suffice to know that the translations are
-- "faithful enough."

-- Public interface for Core --> Sequent Core

-- | Translates a list of Core bindings into Sequent Core.
fromCoreModule :: [Core.CoreBind] -> [SeqCoreBind]
fromCoreModule binds = fromCoreBinds emptySubst binds

-- | Translates a single Core expression as a Sequent Core term.
termFromCoreExpr :: Core.CoreExpr -> SeqCoreTerm
termFromCoreExpr expr
  = fromCoreExprAsTerm freeVarSet expr mkLetContId
  where
    freeVarSet = mkSubst (mkInScopeSet (Core.exprFreeVars expr))
                   emptyVarEnv emptyVarEnv emptyVarEnv

type FromCoreEnv = Subst

-- | Translates a Core expression into Sequent Core.
fromCoreExpr :: FromCoreEnv -> Core.CoreExpr -> SeqCoreCont
                            -> SeqCoreCommand
fromCoreExpr env expr cont = go [] env expr cont
  where
    go binds env expr cont = case expr of
      Core.Var x         -> done $ lookupIdSubst (text "fromCoreExpr") env x
      Core.Lit l         -> done $ Lit l
      Core.App (Core.Var k) e | Var k' <- lookupIdSubst (text "fromCoreExpr") env k, isContId k'
                         -> go binds env e (Return k')
      Core.App e1 e2     ->
        let e2' = fromCoreExprAsTerm env e2 mkArgContId
        in go binds env e1 (App e2' cont)
      Core.Lam x e       -> done $ fromCoreLams env x e
      Core.Let bs e      ->
        let (env', bs') = fromCoreBind env (Just cont) bs
        in go (bs' : binds) env' e cont
      Core.Case e x _ as
        | Return _ <- cont -> let (env_rhs, x') = substBndr env x
                                  as' = map (fromCoreAlt env_rhs cont) as
                              in go binds env e $ Case x' as'
        | otherwise ->
          -- Translating a case naively can duplicate lots of code. Rather than
          -- copy the continuation for each branch, we stuff it into a let
          -- binding and copy only a Return to that binding.
          let k = mkCaseContId (contType cont)
              (env_rhs, x') = substBndr env x
              as' = map (fromCoreAlt env_rhs (Return k)) as
          in go (NonRec k (Cont cont) : binds) env e $ Case x' as'
      Core.Coercion co   -> done $ Coercion (substCo env co)
      Core.Cast e co     -> go binds env e (Cast (substCo env co) cont)
      Core.Tick ti e     -> go binds env e (Tick (substTickish env ti) cont)
      Core.Type t        -> done $ Type (substTy env t)
      where done term = mkCommand (reverse binds) term cont

fromCoreLams :: FromCoreEnv -> Core.CoreBndr -> Core.CoreExpr
                            -> SeqCoreTerm
fromCoreLams env x expr
  = mkLambdas xs' $ body'
  where
    (xs, body) = Core.collectBinders expr
    body' = mkCompute kid $ fromCoreExpr env' body (Return kid)
    (env', xs') = substBndrs env (x : xs)
    kid = mkLamContId ty
    ty  = substTy env' (Core.exprType body)

fromCoreExprAsTerm :: FromCoreEnv -> Core.CoreExpr -> (Type -> ContId)
                                  -> SeqCoreTerm
fromCoreExprAsTerm env expr mkId
  = mkCompute k $ fromCoreExpr env' expr (Return k)
  where
    k  = asContId $ uniqAway (substInScope env) (mkId ty)
    ty = substTy env (Core.exprType expr)
    env' = extendInScope env k

fromCoreLamAsCont :: FromCoreEnv -> SeqCoreCont -> Core.CoreExpr -> Maybe SeqCoreCont
fromCoreLamAsCont env cont (Core.Lam b e)
  = outer e
    where
      (env', b') = substBndr env b
      
      outer :: Core.CoreExpr -> Maybe SeqCoreCont
      outer (Core.App (Core.Var k) e)
                                  | Var k' <- lookupIdSubst (text "fromCoreLamAsCont::outer") env k
                                  , isContTy (idType k')
                                  = inner e (Return k')
      outer (Core.Case e b _ as)  = let (env'', b') = substBndr env' b
                                        cont' = Case b' $ map (fromCoreAlt env'' cont) as
                                    in inner e cont'
      outer body                  = inner body cont
    
      inner :: Core.CoreExpr -> SeqCoreCont -> Maybe SeqCoreCont
      inner (Core.Var x) k          | Var x' <- lookupIdSubst (text "fromCoreLamAsCont::inner") env' x
                                    , x' == b'
                                    = Just k
      inner (Core.App e1 e2) k      = let e2' = fromCoreExprAsTerm env' e2 mkArgContId
                                      in inner e1 (App e2' k)
      inner (Core.Cast e co) k      = inner e (Cast co k)
      inner (Core.Tick ti e) k      = inner e (Tick ti k)
      inner _                _      = Nothing
fromCoreLamAsCont _env _cont other
  = pprPanic "fromCoreLamAsCont" (ppr other)

-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: FromCoreEnv -> SeqCoreCont -> Core.CoreAlt -> SeqCoreAlt
fromCoreAlt env cont (ac, bs, e)
  = let (env', bs') = substBndrs env bs
        e' = fromCoreExpr env' e cont
    in Alt ac bs' e'

-- | Translates a Core binding into Sequent Core.
fromCoreBind :: FromCoreEnv -> Maybe SeqCoreCont -> Core.CoreBind
                            -> (FromCoreEnv, SeqCoreBind)
fromCoreBind env cont_maybe bind =
  case bind of
    Core.NonRec b e |  -- If it's a continuation function, try translating as a
                       -- continuation
                       Just (inTy, _) <- splitContFunTy_maybe (idType b)
                       -- Make sure this isn't a top-level binding; if so, we can't
                       -- keep it as a continuation
                    ,  Just cont      <- cont_maybe
                    ,  let (env', b') = substBndr env (b `setIdType` mkContTy inTy)
                    ,  Just cont'     <- fromCoreLamAsCont env' cont e
                    -> (env', NonRec b' (Cont cont'))
                    |  otherwise
                    -> let b' | Just (inTy, outTy) <- splitContFunTy_maybe (idType b)
                              = b `setIdType` mkFunTy inTy outTy
                              | otherwise
                              = b
                           (env', b'') = substBndr env b'
                           val = fromCoreExprAsTerm env' e mkLetContId
                       in (env', NonRec b'' val)
    Core.Rec pairs  -> let (env', bs') = substRecBndrs env (map fst pairs)
                           vals'       = [fromCoreExprAsTerm env' e mkLetContId
                                           | (_, e) <- pairs]
                       in (env', Rec (zip bs' vals'))

fromCoreBinds :: FromCoreEnv -> [Core.CoreBind] -> [SeqCoreBind]
fromCoreBinds env binds
  = snd $ mapAccumL (\env' -> fromCoreBind env' Nothing) env binds

-- | Translates a command into Core.
commandToCoreExpr :: ContId -> SeqCoreCommand -> Core.CoreExpr
commandToCoreExpr retId cmd = foldr addLet baseExpr (cmdLet cmd)
  where
  addLet b e = Core.mkCoreLet (bindToCore (Just retId) b) e
  baseExpr = contToCoreExpr retId (cmdCont cmd) (termToCoreExpr (cmdTerm cmd))

-- | Translates a term into Core.
termToCoreExpr :: SeqCoreTerm -> Core.CoreExpr
termToCoreExpr val =
  case val of
    Lit l        -> Core.Lit l
    Var x        -> Core.Var x
    Lam x t      -> Core.Lam x (termToCoreExpr t)
    Type t       -> Core.Type t
    Coercion co  -> Core.Coercion co
    Compute kb c -> commandToCoreExpr kb c
    Cont _       -> pprPanic "termToCoreExpr" (ppr val)

-- | Translates a continuation into a function that will wrap a Core expression
-- with a fragment of context (an argument to apply to, a case expression to
-- run, etc.).
contToCoreExpr :: ContId -> SeqCoreCont -> (Core.CoreExpr -> Core.CoreExpr)
contToCoreExpr retId k e =
  case k of
    App  {- expr -} v k'      -> contToCoreExpr retId k' $ Core.mkCoreApp e (termToCoreExpr v)
    Case {- expr -} b as      -> Core.Case e b (contTyArg (idType retId)) (map (altToCore retId) as)
    Cast {- expr -} co k'     -> contToCoreExpr retId k' $ Core.Cast e co
    Tick ti {- expr -} k'     -> contToCoreExpr retId k' $ Core.Tick ti e
    Return x
      | x == retId            -> e
      | otherwise             -> Core.mkCoreApp (Core.Var x') e
      where x' = contIdToCore retId x

contIdToCore :: Id -> ContId -> Id
contIdToCore retId k = k `setIdType` mkContFunTy argTy retTy
  where
    tyOf k = isContTy_maybe (idType k) `orElse` pprPanic "contIdToCore" (pprBndr LetBind k)
    argTy = tyOf k
    retTy = tyOf retId

-- | Translates a binding into Core.
bindToCore :: Maybe ContId -> SeqCoreBind -> Core.CoreBind
bindToCore retId_maybe bind =
  case bind of
    NonRec b (Cont k) -> Core.NonRec b' (Core.Lam x (k' (Core.Var x)))
      where
        b'    = contIdToCore retId b
        x     = setOneShotLambda $ mkContArgId argTy
        k'    = contToCoreExpr retId k
        argTy = isContTy_maybe (idType b) `orElse` pprPanic "bindToCore" (pprBndr LetBind b)
        retId = retId_maybe `orElse` panic "bindToCore: top-level cont"
    NonRec b v        -> Core.NonRec b (termToCoreExpr v)
    Rec bs            -> Core.Rec [ (b, termToCoreExpr v) | (b,v) <- bs ]

-- | Translates a list of top-level bindings into Core.
bindsToCore :: [SeqCoreBind] -> [Core.CoreBind]
bindsToCore binds = map (bindToCore Nothing) binds

altToCore :: ContId -> SeqCoreAlt -> Core.CoreAlt
altToCore retId (Alt ac bs c) = (ac, bs, commandToCoreExpr retId c)

-- Public interface for operations going in both directions

-- | Take an operation on Sequent Core terms and perform it on Core expressions
onCoreExpr :: (SeqCoreTerm -> SeqCoreTerm) -> (Core.CoreExpr -> Core.CoreExpr)
onCoreExpr f = termToCoreExpr . f . termFromCoreExpr

-- | Take an operation on Core expressions and perform it on Sequent Core terms
onSequentCoreTerm :: (Core.CoreExpr -> Core.CoreExpr) -> (SeqCoreTerm -> SeqCoreTerm)
onSequentCoreTerm f = termFromCoreExpr . f . termToCoreExpr