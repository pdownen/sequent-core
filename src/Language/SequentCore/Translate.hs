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
  commandToCoreExpr, termToCoreExpr, kontToCoreExpr,
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
  = fromCoreExprAsTerm freeVarSet expr mkLetKontId
  where
    freeVarSet = mkSubst (mkInScopeSet (Core.exprFreeVars expr))
                   emptyVarEnv emptyVarEnv emptyVarEnv

type FromCoreEnv = Subst

-- | Translates a Core expression into Sequent Core.
fromCoreExpr :: FromCoreEnv -> Core.CoreExpr -> SeqCoreKont
                            -> SeqCoreCommand
fromCoreExpr env expr kont = go [] env expr kont
  where
    go :: [SeqCoreBind] -> FromCoreEnv -> Core.CoreExpr -> SeqCoreKont -> SeqCoreCommand
    go binds env expr kont = case expr of
      Core.Var x         -> done $ lookupIdSubst (text "fromCoreExpr") env x
      Core.Lit l         -> done $ Lit l
      Core.App (Core.Var k) e | Var k' <- lookupIdSubst (text "fromCoreExpr") env k, isKontId k'
                         -> go binds env e (Return k')
      Core.App e1 e2     ->
        let e2' = fromCoreExprAsTerm env e2 mkArgKontId
        in go binds env e1 (App e2' kont)
      Core.Lam x e       -> done $ fromCoreLams env x e
      Core.Let bs e      ->
        let (env', bs') = fromCoreBind env (Just kont) bs
        in go (bs' : binds) env' e kont
      Core.Case e x _ as ->
        -- Translating a case naively can duplicate lots of code. Rather than
        -- copy the continuation for each branch, we bind it to a variable and
        -- copy only a Return to that binding (c.f. makeTrivial in Simpl.hs)
        let k = mkCaseKontId (kontType kont)
            (env_rhs, x') = substBndr env x
            as' = map (fromCoreAlt env_rhs (Return k)) as
        in done $ mkCompute k (go [] env e (Case x' as'))
      Core.Coercion co   -> done $ Coercion (substCo env co)
      Core.Cast e co     -> go binds env e (Cast (substCo env co) kont)
      Core.Tick ti e     -> go binds env e (Tick (substTickish env ti) kont)
      Core.Type t        -> done $ Type (substTy env t)
      where done term = mkCommand (reverse binds) term kont

fromCoreLams :: FromCoreEnv -> Core.CoreBndr -> Core.CoreExpr
                            -> SeqCoreTerm
fromCoreLams env x expr
  = mkLambdas xs' $ body'
  where
    (xs, body) = Core.collectBinders expr
    body' = mkCompute kid $ fromCoreExpr env' body (Return kid)
    (env', xs') = substBndrs env (x : xs)
    kid = mkLamKontId ty
    ty  = substTy env' (Core.exprType body)

fromCoreExprAsTerm :: FromCoreEnv -> Core.CoreExpr -> (Type -> KontId)
                                  -> SeqCoreTerm
fromCoreExprAsTerm env expr mkId
  = mkCompute k $ fromCoreExpr env' expr (Return k)
  where
    k  = asKontId $ uniqAway (substInScope env) (mkId ty)
    ty = substTy env (Core.exprType expr)
    env' = extendInScope env k

fromCoreLamAsKont :: FromCoreEnv -> SeqCoreKont -> Core.CoreExpr -> Maybe SeqCoreKont
fromCoreLamAsKont env kont (Core.Lam b e)
  = outer e
    where
      (env', b') = substBndr env b
      
      outer :: Core.CoreExpr -> Maybe SeqCoreKont
      outer (Core.App (Core.Var k) e)
                                  | Var k' <- lookupIdSubst (text "fromCoreLamAsKont::outer") env k
                                  , isKontTy (idType k')
                                  = inner e (Return k')
      outer (Core.Case e b _ as)  = let (env'', b') = substBndr env' b
                                        kont' = Case b' $ map (fromCoreAlt env'' kont) as
                                    in inner e kont'
      outer body                  = inner body kont
    
      inner :: Core.CoreExpr -> SeqCoreKont -> Maybe SeqCoreKont
      inner (Core.Var x) k          | Var x' <- lookupIdSubst (text "fromCoreLamAsKont::inner") env' x
                                    , x' == b'
                                    = Just k
      inner (Core.App e1 e2) k      = let e2' = fromCoreExprAsTerm env' e2 mkArgKontId
                                      in inner e1 (App e2' k)
      inner (Core.Cast e co) k      = inner e (Cast co k)
      inner (Core.Tick ti e) k      = inner e (Tick ti k)
      inner _                _      = Nothing
fromCoreLamAsKont _env _kont other
  = pprPanic "fromCoreLamAsKont" (ppr other)

-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: FromCoreEnv -> SeqCoreKont -> Core.CoreAlt -> SeqCoreAlt
fromCoreAlt env kont (ac, bs, e)
  = let (env', bs') = substBndrs env bs
        e' = fromCoreExpr env' e kont
    in Alt ac bs' e'

-- | Translates a Core binding into Sequent Core.
fromCoreBind :: FromCoreEnv -> Maybe SeqCoreKont -> Core.CoreBind
                            -> (FromCoreEnv, SeqCoreBind)
fromCoreBind env cont_maybe bind =
  case bind of
    Core.NonRec b e |  -- If it's a continuation function, try translating as a
                       -- continuation
                       Just (inTy, _) <- splitKontFunTy_maybe (idType b)
                       -- Make sure this isn't a top-level binding; if so, we can't
                       -- keep it as a continuation
                    ,  Just kont      <- cont_maybe
                    ,  let (env', b') = substBndr env (b `setIdType` mkKontTy inTy)
                    ,  Just kont'     <- fromCoreLamAsKont env' kont e
                    -> (env', NonRec (BindKont b' kont'))
                    |  otherwise
                    -> let b' | Just (inTy, outTy) <- splitKontFunTy_maybe (idType b)
                              = b `setIdType` mkFunTy inTy outTy
                              | otherwise
                              = b
                           (env', b'') = substBndr env b'
                           val = fromCoreExprAsTerm env' e mkLetKontId
                       in (env', NonRec (BindTerm b'' val))
    Core.Rec pairs  -> let (env', bs') = substRecBndrs env (map fst pairs)
                           vals'       = [fromCoreExprAsTerm env' e mkLetKontId
                                           | (_, e) <- pairs]
                       in (env', Rec (zipWith BindTerm bs' vals'))

fromCoreBinds :: FromCoreEnv -> [Core.CoreBind] -> [SeqCoreBind]
fromCoreBinds env binds
  = snd $ mapAccumL (\env' -> fromCoreBind env' Nothing) env binds

-- | Translates a command into Core.
commandToCoreExpr :: KontId -> SeqCoreCommand -> Core.CoreExpr
commandToCoreExpr retId cmd = foldr addLet baseExpr (cmdLet cmd)
  where
  addLet b e = Core.mkCoreLet (bindToCore (Just retId) b) e
  baseExpr = kontToCoreExpr retId (cmdKont cmd) (termToCoreExpr (cmdTerm cmd))

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

-- | Translates a continuation into a function that will wrap a Core expression
-- with a fragment of context (an argument to apply to, a case expression to
-- run, etc.).
kontToCoreExpr :: KontId -> SeqCoreKont -> (Core.CoreExpr -> Core.CoreExpr)
kontToCoreExpr retId k e =
  case k of
    App  {- expr -} v k'      -> kontToCoreExpr retId k' $ Core.mkCoreApp e (termToCoreExpr v)
    Case {- expr -} b as      -> Core.Case e b (kontTyArg (idType retId)) (map (altToCore retId) as)
    Cast {- expr -} co k'     -> kontToCoreExpr retId k' $ Core.Cast e co
    Tick ti {- expr -} k'     -> kontToCoreExpr retId k' $ Core.Tick ti e
    Return x
      | x == retId            -> e
      | otherwise             -> Core.mkCoreApp (Core.Var x') e
      where x' = kontIdToCore retId x

kontIdToCore :: Id -> KontId -> Id
kontIdToCore retId k = k `setIdType` mkKontFunTy argTy retTy
  where
    tyOf k = isKontTy_maybe (idType k) `orElse` pprPanic "kontIdToCore" (pprBndr LetBind k)
    argTy = tyOf k
    retTy = tyOf retId

-- | Translates a binding into Core.
bindToCore :: Maybe KontId -> SeqCoreBind -> Core.CoreBind
bindToCore retId_maybe bind =
  case bind of
    NonRec pair -> Core.NonRec b v where (b, v) = bindPairToCore retId_maybe pair
    Rec pairs   -> Core.Rec (map (bindPairToCore retId_maybe) pairs)

bindPairToCore :: Maybe KontId -> SeqCoreBindPair -> (Core.CoreBndr, Core.CoreExpr)
bindPairToCore retId_maybe pair =
  case pair of
    BindTerm b v -> (b, termToCoreExpr v)
    BindKont b k -> (b', Core.Lam x (k' (Core.Var x)))
      where
        b'    = kontIdToCore retId b
        x     = setOneShotLambda $ mkKontArgId argTy
        k'    = kontToCoreExpr retId k
        argTy = isKontTy_maybe (idType b) `orElse` pprPanic "bindToCore" (pprBndr LetBind b)
        retId = retId_maybe `orElse` panic "bindToCore: top-level cont"
    

-- | Translates a list of top-level bindings into Core.
bindsToCore :: [SeqCoreBind] -> [Core.CoreBind]
bindsToCore binds = map (bindToCore Nothing) binds

altToCore :: KontId -> SeqCoreAlt -> Core.CoreAlt
altToCore retId (Alt ac bs c) = (ac, bs, commandToCoreExpr retId c)

-- Public interface for operations going in both directions

-- | Take an operation on Sequent Core terms and perform it on Core expressions
onCoreExpr :: (SeqCoreTerm -> SeqCoreTerm) -> (Core.CoreExpr -> Core.CoreExpr)
onCoreExpr f = termToCoreExpr . f . termFromCoreExpr

-- | Take an operation on Core expressions and perform it on Sequent Core terms
onSequentCoreTerm :: (Core.CoreExpr -> Core.CoreExpr) -> (SeqCoreTerm -> SeqCoreTerm)
onSequentCoreTerm f = termFromCoreExpr . f . termToCoreExpr