{-# LANGUAGE ParallelListComp, TupleSections #-}

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

import Language.SequentCore.Syntax
import Language.SequentCore.WiredIn

import CoreSubst
import qualified CoreSyn as Core
import qualified CoreUtils as Core
import qualified CoreFVs as Core
import Id
import Maybes
import qualified MkCore as Core
import Outputable  hiding ( (<>) )
import Type        hiding ( substTy )
import VarEnv
import VarSet

import Control.Arrow ( (+++) ) 
import Data.List
import Data.Monoid

-- $txn
-- The translations to and from Sequent Core are /not/ guaranteed to be perfect
-- inverses. However, any differences between @e@ and @commandToCoreExpr
-- (fromCoreExpr e)@ should be operationally insignificant, such as a @let@
-- floating out from a function being applied. A more precise characterization
-- of the indended invariants of these functions would entail some sort of
-- /bisimulation/, but it should suffice to know that the translations are
-- "faithful enough."

------------------------------------------------
-- Public interface for Core --> Sequent Core --
------------------------------------------------

-- | Translates a list of Core bindings into Sequent Core.
fromCoreModule :: [Core.CoreBind] -> [SeqCoreBind]
fromCoreModule binds = unmarkProgram $ fromCoreBinds binds

-- | Translates a single Core expression as a Sequent Core term.
termFromCoreExpr :: Core.CoreExpr -> SeqCoreTerm
termFromCoreExpr expr
  = unmarkTerm initUnmarkEnv . snd $ fromCoreExprAsTerm env expr mkLetKontId
  where
    env = FCE { fce_subst = freeVarSet, fce_currentKont = Nothing
              , fce_boundKonts = emptyVarSet }
    freeVarSet = mkSubst (mkInScopeSet (Core.exprFreeVars expr))
                   emptyVarEnv emptyVarEnv emptyVarEnv

---------------------------------------------------
-- Phase 1: Translate, contifying optimistically --
---------------------------------------------------

data FromCoreEnv
  = FCE { fce_subst :: Subst
        , fce_currentKont :: Maybe KontId
        , fce_boundKonts :: VarSet
        }

initFromCoreEnv :: FromCoreEnv
initFromCoreEnv = FCE { fce_subst = emptySubst
                      , fce_currentKont = Nothing
                      , fce_boundKonts = emptyVarSet }

bindAsKont :: FromCoreEnv -> KontId -> FromCoreEnv
bindAsKont env p = env { fce_boundKonts = fce_boundKonts env `extendVarSet` p }

bindCurrentKont :: FromCoreEnv -> KontId -> FromCoreEnv
-- Once a new current continuation is bound, all let-bound continuations become
-- inaccessible
bindCurrentKont env p = env { fce_subst = fce_subst env `extendInScope` p
                            , fce_boundKonts = emptyVarSet
                            , fce_currentKont = Just p }

isKontIn :: Var -> FromCoreEnv -> Bool
x `isKontIn` FCE { fce_currentKont = currKont, fce_boundKonts = bound }
  = Just x == currKont || x `elemVarSet` bound

data IdUsage
  = IU { iu_asFunc :: Bool
       , iu_asKont :: Bool }

usedAsKont, usedAsFunc :: Var -> FromCoreResults
usedAsFunc x = FCR $ unitVarEnv x $ IU { iu_asFunc = True,  iu_asKont = False }
usedAsKont x = FCR $ unitVarEnv x $ IU { iu_asFunc = False, iu_asKont = True  }

instance Monoid IdUsage where
  mempty = IU False False
  mappend (IU af1 ak1) (IU af2 ak2) = IU (af1 || af2) (ak1 || ak2)

newtype FromCoreResults
  = FCR { fcr_usages :: VarEnv IdUsage }
  
instance Monoid FromCoreResults where
  mempty = FCR emptyVarEnv
  mappend (FCR u1) (FCR u2) = FCR (plusVarEnv_C mappend u1 u2)

without :: FromCoreResults -> Var -> FromCoreResults
FCR u `without` x = FCR (u `delVarEnv` x)

withoutList :: FromCoreResults -> [Var] -> FromCoreResults
FCR u `withoutList` xs = FCR (u `delVarEnvList` xs)

-- See Note [Failure modes for contification]
data Mark
  = Keep
  | KeepNote SDoc
  | UnKontify
  | UnKontifyIf [Var] Type (Term MarkedVar)

data MarkedVar = Marked { mv_var :: Var, mv_mark :: Mark }

instance HasId MarkedVar where
  identifier = mv_var

lookupIdSubstForId :: SDoc -> Subst -> Id -> Id
lookupIdSubstForId doc subst id
  = case lookupIdSubst doc subst id of
      Core.Var id' -> id'
      other -> pprPanic "lookupIdSubstForId" (ppr id <+> darrow <+> ppr other)

fromCoreExpr :: FromCoreEnv -> Core.CoreExpr -> Kont MarkedVar
                            -> (FromCoreResults, Command MarkedVar)
fromCoreExpr env expr kont = go [] mempty env expr kont
  where
    FCE { fce_subst = subst } = env
  
    go :: [Bind MarkedVar] -> FromCoreResults -> FromCoreEnv -> Core.CoreExpr
       -> Kont MarkedVar -> (FromCoreResults, Command MarkedVar)
    go binds results env expr kont = case expr of
      Core.Var x         -> done results' $ Var x'
        where
          x'              = lookupIdSubstForId (text "fromCoreExpr/Var") subst x
          results'        = results <> usedAsFunc x'
      Core.Lit l         -> done results $ Lit l
      Core.App (Core.Var p) e
        -- Is it a tail call to a known continuation? It's a tail call if kont
        -- is the current continuation.
        | Core.Var p' <- lookupIdSubst (text "fromCoreExpr/App/Var") subst p
        , p' `isKontIn` env
        , Just q <- fce_currentKont env
        , Return q' <- kont
        , q == q'
                         -> go binds (results <> usedAsKont p') env e $ Return p'
      Core.App e1 e2     ->
        let (res_e2, e2') = fromCoreExprAsTerm env e2 mkArgKontId
        in go binds (results <> res_e2) env e1 (App e2' kont)
      Core.Lam x e       ->
        let (res, comm) = fromCoreLams env x e
        in done (results <> res) comm
      Core.Let bs e      ->
        -- Note the knot-tying. Dependencies: res'' and comm depend on env';
        -- res' and bs' depend on res''.
        let (res', env', bs') = fromCoreBind env (Just kont) res'' bs
            (res'', comm)     = go (bs' : binds) mempty env' e kont
        in ((results <> res' <> res'') `withoutList` map mv_var (bindersOf bs'), comm)
      Core.Case e x _ as 
        | Return {} <- kont ->
        let (subst_rhs, x') = substBndr subst x
            env_rhs = env { fce_subst = subst_rhs }
            (res', as') = unzip $ map (fromCoreAlt env_rhs kont) as
            res'' = mconcat res' `without` x
        in go binds (results <> res'') env e (Case (Marked x' Keep) as')
        | otherwise ->
        -- Translating a case naively can duplicate lots of code. Rather than
        -- copy the continuation for each branch, we bind it to a variable and
        -- copy only a Return to that binding (c.f. makeTrivial in Simpl.hs)
        let (subst', p) = substBndr subst (mkCaseKontId (kontType kont))
            (subst_rhs, x') = substBndr subst' x
            env' = env `bindAsKont` p
            env_rhs = env' { fce_subst = subst_rhs }
            (res', as') = unzip $ map (fromCoreAlt env_rhs (Return p)) as
            res'' = mconcat res' `withoutList` [x, p]
            kontBind = NonRec (BindKont (Marked p Keep) kont)
        in go (kontBind : binds) (results <> res'') env' e (Case (Marked x' Keep) as')
      Core.Coercion co   -> done results $ Coercion (substCo (fce_subst env) co)
      Core.Cast e co     -> go binds results env e (Cast (substCo (fce_subst env) co) kont)
      Core.Tick ti e     -> go binds results env e (Tick (substTickish (fce_subst env) ti) kont)
      Core.Type t        -> done results $ Type (substTy (fce_subst env) t)
      where done results term = (results, mkCommand (reverse binds) term kont)

fromCoreLams :: FromCoreEnv -> Core.CoreBndr -> Core.CoreExpr
                            -> (FromCoreResults, Term MarkedVar)
fromCoreLams env x expr
  = (bodyRes `withoutList` (kid : xs'), mkLambdas xs'' body')
  where
    (xs, body) = Core.collectBinders expr
    (bodyRes, bodyComm) = fromCoreExpr env' body (Return kid)
    body' = mkCompute (Marked kid Keep) bodyComm
    (subst', xs') = substBndrs (fce_subst env) (x : xs)
    xs'' = [ Marked x Keep | x <- xs' ]
    env' = env { fce_subst = subst' } `bindCurrentKont` kid
    kid = mkLamKontId ty
    ty  = substTy subst' (Core.exprType body)

fromCoreExprAsTerm :: FromCoreEnv -> Core.CoreExpr -> (Type -> KontId)
                                  -> (FromCoreResults, Term MarkedVar)
fromCoreExprAsTerm env expr mkId
  = (res', mkCompute (Marked k Keep) body)
  where
    (res, body) = fromCoreExpr env' expr (Return k)
    res' = res `without` k
    subst = fce_subst env
    k  = asKontId $ uniqAway (substInScope subst) (mkId ty)
    ty = substTy subst (Core.exprType expr)
    env' = env `bindCurrentKont` k

fromCoreLamAsKont :: FromCoreEnv -> Kont MarkedVar -> Core.CoreExpr
                  -> Maybe (FromCoreResults, Kont MarkedVar)
fromCoreLamAsKont env kont (Core.Lam b e)
  = outer e
    where
      subst = fce_subst env
      (subst', b') = substBndr subst b
      env' = env { fce_subst = subst' }
      
      outer :: Core.CoreExpr -> Maybe (FromCoreResults, Kont MarkedVar)
      outer (Core.App (Core.Var k) e)
                                  | Core.Var k' <- lookupIdSubst (text "fromCoreLamAsKont::outer") subst k
                                  , k' `elemVarSet` fce_boundKonts env
                                  = inner e (usedAsKont k') (Return k')
      outer (Core.Case e b _ as)  = let (subst'', b') = substBndr subst' b
                                        env'' = env' { fce_subst = subst'' }
                                        (res, as') = unzip $ map (fromCoreAlt env'' kont) as
                                        kont' = Case (Marked b' Keep) as'
                                    in inner e (mconcat res) kont'
      outer body                  = inner body mempty kont
    
      inner :: Core.CoreExpr -> FromCoreResults -> Kont MarkedVar -> Maybe (FromCoreResults, Kont MarkedVar)
      inner (Core.Var x) res k      | Core.Var x' <- lookupIdSubst (text "fromCoreLamAsKont::inner") subst' x
                                    , x' == b'
                                    = Just (res <> usedAsFunc x', k)
      inner (Core.App e1 e2) res k  = let (res', e2') = fromCoreExprAsTerm env' e2 mkArgKontId
                                      in inner e1 (res <> res') (App e2' k)
      inner (Core.Cast e co) res k  = inner e res (Cast co k)
      inner (Core.Tick ti e) res k  = inner e res (Tick ti k)
      inner _                _   _  = Nothing
fromCoreLamAsKont env _kont (Core.Var p)
  | Core.Var p' <- lookupIdSubst (text "fromCoreLamAsKont/Core.Var") (fce_subst env) p
  = Just (usedAsKont p', Return p')
fromCoreLamAsKont _env _kont _other
  = Nothing

-- | Translates a Core case alternative into Sequent Core.
fromCoreAlt :: FromCoreEnv -> Kont MarkedVar -> Core.CoreAlt
            -> (FromCoreResults, Alt MarkedVar)
fromCoreAlt env kont (ac, bs, e)
  = let (subst', bs') = substBndrs (fce_subst env) bs
        (res, e') = fromCoreExpr (env { fce_subst = subst' }) e kont
    in (res, Alt ac [Marked b Keep | b <- bs']  e')

{-

Note [Failure modes for contification]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Consider the binding:

  let f = e1 in e2

If f can be translated as a continuation, we do so on an optimistic basis.
However, if e2 ever invokes it in a way that does not translate as a
continuation invocation, we must undo our optimism. There are five cases:

1. The RHS, e1, does not translate as a continuation. We translate it as a
   function to begin with, marking the binding as Keep.
2. The RHS translates as a continuation, but e2 only uses it as a function,
   meaning that no invocation of f can be translated as a continuation
   invocation. Again, we use the function translation and mark the binding as
   Keep.
3. The RHS translates as a continuation and e2 uses it as a function in one
   place and as a continuation in another. We have to use the function
   translation; furthermore, we have to mark the binding as UnKontify so that
   the second pass knows to change those invocations to function calls.
4. The RHS translates as a continuation and e2 only uses it that way, *but* the
   translation assumed that certain variables bound continuations, so if any of
   those wind up being uncontified, so does f. We use the continuation
   translation provisionally, but we mark the binding UnkontifyIf vars ty e1',
   where vars is a list of let-bound continuations used by e1, ty is the
   original type of the binder, and e1' is the translation of e1 as a function
   instead of a continuation. This way the second pass has all the information
   to make the switch on the fly if it needs to.
5. The RHS translates as a continuation, e2 only uses it as such, and no
   let-bound continuation variables are used by e1. In this case (and only this
   case), we commit to the continuation translation and mark the binding Keep.
-}

-- | Translates a Core binding into Sequent Core. Note that the FromCoreResults
-- argument is the results from translating the *scope* of the binding, which
-- necessarily depends on the FromCoreEnv returned here, so there is knot-tying
-- going on. The caller must be careful that the FromCoreResults parameter does
-- NOT depend strictly on the value of the returned Bind or that of the 
-- returned result environment.
fromCoreBind :: FromCoreEnv -> Maybe (Kont MarkedVar) -> FromCoreResults
             -> Core.CoreBind -> (FromCoreResults, FromCoreEnv, Bind MarkedVar)
fromCoreBind (env@FCE { fce_subst = subst }) kont_maybe scopeRes bind =
  case bind of
    Core.NonRec x e -> (bodyRes, env_scope, bind_final)
      where
        (subst', x') = substBndr subst x
        env' = env { fce_subst = subst' }
        
        -- See Note [Failure modes for contification] for cases.
        
        -- The function translation, used in cases 1-3 and potentially 4.
        (funcRes, rhsAsFunc) = fromCoreExprAsTerm env' e mkLetKontId
        
        -- The continuation translation, used in cases 4 and 5.
        rhsAsKont_maybe = kont_maybe >>= \kont -> fromCoreLamAsKont env' kont e
        
        -- If False, we are in case 1 (see Note [Failure modes for contification]).
        couldBeKont = isJust rhsAsKont_maybe
        
        -- Convenient bindings (only good if couldBeKont is True)
        Just (kontRes, rhsAsKont) = rhsAsKont_maybe
        
        -- If we might return a continuation binding, optimistically return an
        -- environment that says we are. The second pass is there to clean up
        -- if this goes sideways. (We can't look at scopeRes to determine this
        -- since, by knot-tying shenanigans, scopeRes may depend on env_scope!)
        env_scope
          | couldBeKont = env' `bindAsKont` x'
          | otherwise   = env'
        
        ----------------------------------
        -- scopeRes causality threshold --
        ----------------------------------
        
        -- Nothing above the threshold is allowed to depend on scopeRes. Then,
        -- the caller of this function is not allowed to have scopeRes depend
        -- on bind_final. Thus we are safe to allow bind_final to depend on
        -- scopeRes.
        
        -- Is the bound variable used as a function (cases 2 and 3) or as a
        -- continuation (cases 3-5)? Both may be true (case 3).
        (usedAsFunc, usedAsKont)
          | Just usage <- lookupVarEnv (fcr_usages scopeRes) x'
          = (iu_asFunc usage, iu_asKont usage)
          | otherwise
          = (False, False)
        
        -- Should we return the continuation, and how should we mark the id?
        (returnKont, mark)
          | not couldBeKont        = (False, KeepNote (text "no translation"))    -- case 1
          | not usedAsKont         = (False, KeepNote (text "not used as cont"))  -- case 2
          | usedAsKont, usedAsFunc = (False, UnKontify)                           -- case 3
          | not (null usedKontIds) = (True,  UnKontifyIf usedKontIds (idType x') rhsAsFunc) -- case 4
          | otherwise              = (True,  KeepNote (text "used only as cont")) -- case 5
          where
            usedKontIds | Just (res, _) <- rhsAsKont_maybe
                        = let ins = substInScope subst
                          in filterVarEnvKeysAmong ins iu_asKont (fcr_usages res)
                        | otherwise
                        = []
        
        (bindPair, bodyRes, x'')
          | returnKont = (BindKont marked rhsAsKont, kontRes, idToKontId x')
          | otherwise  = (BindTerm marked rhsAsFunc, funcRes, x')
          where marked = Marked x'' mark
        
        bind_final = NonRec bindPair

    -- TODO Contify recursive functions as well
    Core.Rec pairs  -> let (subst', bs') = substRecBndrs (fce_subst env) (map fst pairs)
                           env'          = env { fce_subst = subst' }
                           (res, vals')  = unzip [fromCoreExprAsTerm env' e mkLetKontId
                                                 | (_, e) <- pairs]
                       in (mconcat res, env', Rec [BindTerm (Marked b' Keep) val'
                                                  | b' <- bs'
                                                  | val' <- vals'])

idToKontId :: Id -> KontId
idToKontId p
  | Just (argTy, _retTy) <- splitFunTy_maybe (idType p)
  = p `setIdType` mkKontTy argTy
  | otherwise
  = pprPanic "idToKontId" (ppr p)

filterVarEnvKeysAmong :: InScopeSet -> (a -> Bool) -> VarEnv a -> [Var]
filterVarEnvKeysAmong ins pr env = mapMaybe (lookupInScope_Directly ins) uniqs
  where uniqs = varEnvKeys (filterVarEnv pr env)

fromCoreBinds :: [Core.CoreBind] -> [Bind MarkedVar]
fromCoreBinds = snd . go initFromCoreEnv
  where
    go env (bind:binds)
      = (res <> res', bind':binds')
      where
        (res, env', bind') = fromCoreBind env Nothing res' bind
        (res', binds')     = go env' binds
    go _ []
      = (mempty, [])

-------------------------------------------
-- Phase 2: Decontify marked identifiers --
-------------------------------------------

data UnmarkEnv = UE { ue_inScope     :: InScopeSet
                    , ue_conv        :: VarSet
                    , ue_currentKont :: Maybe KontId }

initUnmarkEnv :: UnmarkEnv
initUnmarkEnv = UE { ue_inScope = emptyInScopeSet
                   , ue_conv    = emptyVarSet
                   , ue_currentKont = Nothing }

unmarkProgram :: Program MarkedVar -> SeqCoreProgram
unmarkProgram pgm = snd . mapAccumL unmarkBind initUnmarkEnv $ pgm

keep :: Mark -> Bool
keep Keep          = True
keep (KeepNote {}) = True
keep _             = False

unmarkBind :: UnmarkEnv -> Bind MarkedVar -> (UnmarkEnv, SeqCoreBind)
-- See [Failure modes of contification]
-- A bound term is in one of cases 1-3
unmarkBind env (NonRec (BindTerm (Marked x mark) term))
  = (env', NonRec (BindTerm x (unmarkTerm env' term)))
  where
    env' = env { ue_inScope = ue_inScope env `extendInScopeSet` x
               , ue_conv    = conv' }
    conv' | keep mark    = ue_conv env -- case 1 or 2
          | otherwise    = ue_conv env `extendVarSet` x -- case 3
-- A bound continuation is in case 4 or case 5
unmarkBind env (NonRec (BindKont (Marked p mark) _kont))
  | UnKontifyIf vars ty term <- mark -- case 4 (failure)
  , any (`elemVarEnv` ue_conv env) vars
  -- Pretend we have been in case 3 all along
  = unmarkBind env (NonRec (BindTerm (Marked (p `setIdType` ty) UnKontify) term))
unmarkBind env (NonRec (BindKont (Marked p _mark) kont)) -- case 4 (success) or 5
  = (env', NonRec (BindKont p (unmarkKont env' kont)))
  where
    env' = env { ue_inScope = ue_inScope env `extendInScopeSet` p }
-- TODO: When we contify recursive functions, handle them here
unmarkBind env (Rec pairs)
  = (env', Rec pairs')
  where
    env' = env { ue_inScope = ue_inScope env `extendInScopeSetList` map (mv_var . binderOfPair) pairs }
    pairs' = [ mkBindPair x ((unmarkTerm env' +++ unmarkKont env') rhs)
             | pair <- pairs, let (Marked x _, rhs) = destBindPair pair ]


unmarkTerm :: UnmarkEnv -> Term MarkedVar -> SeqCoreTerm
unmarkTerm env term
  = case term of
      Var x          -> Var (lookupInScope (ue_inScope env) x `orElse` x)
      Lam x body     -> Lam x' (unmarkTerm (envWith x') body)            where x' = mv_var x
      Compute p comm -> Compute p' (unmarkCommand (envWithKont p') comm) where p' = mv_var p
      Lit lit        -> Lit lit
      Type ty        -> Type ty
      Coercion co    -> Coercion co
  where
    envWith x = env { ue_inScope = ue_inScope env `extendInScopeSet` x }
    envWithKont p = (envWith p) { ue_currentKont = Just p }

unmarkKont :: UnmarkEnv -> Kont MarkedVar -> SeqCoreKont
unmarkKont env kont
  = case kont of
      Return p
        -- Sanity check: If we needed to convert p, it's too late now
        | p `elemVarSet` ue_conv env
        -> pprPanic "unmarkKont" (ppr p)
        | otherwise
        -> Return (lookupInScope (ue_inScope env) p `orElse` p)
      App v k     -> App (unmarkTerm env v) (unmarkKont env k)
      Case x alts -> Case x' (map (unmarkAlt (envWith x')) alts) where x' = mv_var x
      Cast co k   -> Cast co (unmarkKont env k)
      Tick ti k   -> Tick ti (unmarkKont env k)
  where
    envWith x = env { ue_inScope = ue_inScope env `extendInScopeSet` x }

unmarkAlt :: UnmarkEnv -> Alt MarkedVar -> SeqCoreAlt
unmarkAlt env (Alt altCon xs rhs)
  = Alt altCon xs' (unmarkCommand env' rhs)
  where
    xs'  = map mv_var xs
    env' = env { ue_inScope = ue_inScope env `extendInScopeSetList` xs' }

unmarkCommand :: UnmarkEnv -> Command MarkedVar -> SeqCoreCommand
unmarkCommand env (Command { cmdLet = binds, cmdTerm = term, cmdKont = kont })
  = mkCommand binds' term' kont'
  where
    (env', binds') = mapAccumL unmarkBind env binds
    (term', kont') = unmarkCut env' term kont

unmarkCut :: UnmarkEnv -> Term MarkedVar -> Kont MarkedVar
          -> (SeqCoreTerm, SeqCoreKont)
unmarkCut env term kont
  | Just (kk, p) <- kontAsReturn kont
  , p `elemVarSet` ue_conv env
  = let curr = ue_currentKont env `orElse` pprPanic "unmarkCut" (ppr kont)
        arg  = mkCompute q (mkCommand [] (unmarkTerm env' term)
                                         (unmarkKont env' (kk (Return q))))
        q    = mkArgKontId (termType term)
        env' = env { ue_currentKont = Just q }
    in (Var p, App arg (Return curr))
unmarkCut env term kont
  = (unmarkTerm env term, unmarkKont env kont)
  
kontAsReturn :: Kont b -> Maybe (Kont b -> Kont b, KontId)
kontAsReturn = go (\kont' -> kont')
  where
    go kk (Return p)  = Just (kk, p)
    go kk (App v k)   = go (kk . App v)   k
    go kk (Cast co k) = go (kk . Cast co) k
    go kk (Tick ti k) = go (kk . Tick ti) k
    go _  (Case {})   = Nothing

------------------------------------------------
-- Public interface for Sequent Core --> Core --
------------------------------------------------
    
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
kontIdToCore retId k = k `setIdType` mkFunTy argTy retTy
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

--------------------------------------------------------------
-- Public interface for operations going in both directions --
--------------------------------------------------------------

-- | Take an operation on Sequent Core terms and perform it on Core expressions
onCoreExpr :: (SeqCoreTerm -> SeqCoreTerm) -> (Core.CoreExpr -> Core.CoreExpr)
onCoreExpr f = termToCoreExpr . f . termFromCoreExpr

-- | Take an operation on Core expressions and perform it on Sequent Core terms
onSequentCoreTerm :: (Core.CoreExpr -> Core.CoreExpr) -> (SeqCoreTerm -> SeqCoreTerm)
onSequentCoreTerm f = termFromCoreExpr . f . termToCoreExpr

----------------
-- Miscellany --
----------------

instance Outputable Mark where
  ppr Keep           = text "keep"
  ppr (KeepNote doc) = text "keep:" <+> doc
  ppr UnKontify      = text "uncont"
  ppr (UnKontifyIf ids _ _) = text "uncont if" <+> ppr ids

instance Outputable MarkedVar where
  ppr (Marked var mark) = ppr var <+> brackets (ppr mark)

instance OutputableBndr MarkedVar where
  pprBndr site (Marked var Keep) = pprBndr site var
  pprBndr site (Marked var mark) = pprBndr site var <+> brackets (ppr mark)
  pprPrefixOcc (Marked var _) = pprPrefixOcc var
  pprInfixOcc  (Marked var _) = pprInfixOcc  var
