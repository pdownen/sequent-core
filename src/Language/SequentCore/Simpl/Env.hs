{-# LANGUAGE ViewPatterns, BangPatterns, FlexibleInstances, CPP #-}

module Language.SequentCore.Simpl.Env (
  -- * Simplifier context
  SimplEnv, SimplTermEnv, CallCtxt(..),
  initialEnv, getMode, updMode, dynFlags, getSimplRules, getFamEnvs,
  getUnfoldingInRuleMatch, activeRule, getInScopeSet,
  
  -- * Substitution and lexical scope
  SubstAns(..), KontSubst, Substable(..),
  substId, substPv, substKv, substTy, substTyVar, substCo, substCoVar, lookupRecBndr,
  substTerm, substKont, substFrame, substEnd, substJoin, substCommand,
  extendIdSubst, extendJvSubst, extendTvSubst, extendCvSubst,
  extendSubstWithInBindPair, extendSubstWithOutBindPair,
  setRetKont, pushKont,
  enterScope, enterKontScope, enterRecScopes, enterLamScope, enterLamScopes, mkFreshVar,
  retType, getContext, setContext,
  addBndrRules,
  getTvSubst, getCvSubst,
  zapSubstEnvs, zapKontSubstEnvs, zapKontSubstEnvsStatic,
  
  -- * Extracting the part of the context carrying lexically scoped information
  StaticEnv, StaticTermEnv,
  staticPart, termStaticPart, narrowToStaticTermPart,
  setStaticPart, setStaticTermPart,
  inDynamicScope, inDynamicScopeForTerm,
  emptyStaticEnv, emptyStaticTermEnv,
  
  -- * Objects with lexical scope information attached
  Scoped(..), DupFlag(..),
  ScopedFrame, ScopedEnd, ScopedJoin, ScopedCommand,
  openScoped, unScope, substScoped,
  okToDup,
  pprMultiScopedKont,
  
  -- * Generalized notion of continuation
  MetaKont(..),
  canDupMetaKont,
  
  -- * Sequent Core definitions (unfoldings) of identifiers
  IdDefEnv, Definition(..), UnfoldingGuidance(..),
  mkBoundToTerm, mkBoundToTermWithGuidance, termInlineBoringOk, mkTermDef,
  mkBoundToJoin, mkBoundToJoinWithGuidance, joinInlineBoringOk, mkJoinDef,
  mkBoundToDFun,
  findDef, findRealDef, setDef, activeUnfolding,
  defIsCheap, defIsConLike, defIsEvald, defIsSmallEnoughToInline, defIsStable,
  
  -- * Definitions floating outward
  Floats,
  emptyFloats, unitFloat, addNonRecFloat, addRecFloats, addFloats, catFloats, addingFloats,
  mapFloats, extendFloats, wrapFloats, wrapKontFloats, wrapFloatsAroundTerm,
  isEmptyFloats, hasNoKontFloats, zapKontFloats,
  doFloatFromRhs, getFloatBinds,
  augmentFromFloats,
  
  -- * Type synonyms distinguishing incoming (unsubstituted) syntax from outgoing
  In, InCommand, InTerm, InArg, InKont, InFrame, InEnd, InJoin,
  InAlt, InBind, InBndr, InBindPair,
  InType, InCoercion, InId, InJoinId, InVar, InTyVar, InCoVar,
  Out, OutCommand, OutTerm, OutArg, OutKont, OutFrame, OutEnd, OutJoin,
  OutAlt, OutBind, OutBndr, OutBindPair,
  OutType, OutCoercion, OutId, OutJoinId, OutVar, OutTyVar, OutCoVar,
  SubstedCoercion,
  
  -- * Term information
  termIsHNF, termIsConLike, termIsConApp_maybe,
  
  -- * Output
  pprTermEnv
) where

import Language.SequentCore.Arity
import Language.SequentCore.OccurAnal
import Language.SequentCore.Simpl.ExprSize
import {-# SOURCE #-} Language.SequentCore.Simpl.Util
import Language.SequentCore.Syntax
import Language.SequentCore.Translate

import BasicTypes ( Activation, Arity, CompilerPhase(..), PhaseNum
                  , TopLevelFlag(..), RecFlag(..)
                  , isActive, isActiveIn, isEarlyActive
                  , isInlinePragma, inlinePragmaActivation
                  , isTopLevel, isNotTopLevel, isNonRec )
import Coercion   ( Coercion, CvSubstEnv, CvSubst(..)
                  , coercionKind, decomposeCo, isReflCo
                  , liftCoSubstWith, mkReflCo, mkTransCo )
import CoreFVs
import qualified Coercion
import CoreMonad  ( SimplifierMode(..) )
import qualified CoreSubst
import CoreSyn    ( Tickish(Breakpoint)
                  , Unfolding(..), UnfoldingGuidance(..), UnfoldingSource(..)
                  , hasSomeUnfolding, isCompulsoryUnfolding, isStableSource, mkOtherCon
                  , tickishCounts, tickishIsCode )
import qualified CoreSyn as Core
import CoreUnfold ( CallCtxt(..), mkCoreUnfolding, mkDFunUnfolding )
import DataCon
import DynFlags   ( DynFlags, ufCreationThreshold, ufUseThreshold )
import FamInstEnv ( FamInstEnv )
import FastString ( FastString )
import Id
import IdInfo
import Maybes
import OrdList
import Outputable
import Pair
import Rules      ( RuleBase )
import TyCon
import Type       ( Type, TvSubstEnv, TvSubst
                  , eqType, seqType, splitTyConApp_maybe, tyVarsOfType
                  , mkTvSubst, mkTyConApp )
import qualified Type
import UniqSupply
import Util       ( debugIsOn
                  , count, dropList, equalLength, takeList, splitAtList )
import Var
import VarEnv
import VarSet

import Control.Applicative ( (<$>) )
import Control.Exception   ( assert )
import Data.List           ( mapAccumL )

infixl 1 `setStaticPart`, `inDynamicScope`, `setRetKont`

-- | The context of a piece of code.
data SimplEnv
  = SimplEnv    { se_idSubst :: SimplIdSubst   -- InId      |--> TermSubstAns (in/out)
                , se_tvSubst :: TvSubstEnv     -- InTyVar   |--> OutType
                , se_cvSubst :: CvSubstEnv     -- InCoVar   |--> OutCoercion
                --  ^^^ term static part ^^^  --
                -- No bindings for join-points

                , se_jvSubst :: SimplJvSubst   -- InJoinId  |--> PKontSubstAns (in/out)
                , se_retTy   :: Maybe OutType
                , se_retKont :: KontSubst      -- ()        |--> MetaKont (in/out)
                --  ^^^ static part ^^^  --
                --  (includes term static part plus bindings for join points

                , se_inScope :: InScopeSet     -- OutVar    |--> OutVar
                , se_defs    :: IdDefEnv       -- OutId     |--> Definition (out)
                                               -- Gives the unfoldings in Sequent Core
                                               -- for Ids in the InScopeSet
                                               -- INVARIANT: dom(se_defs) is a subset of dom(se_inScope)
                , se_context :: CallCtxt
                , se_global  :: SimplGlobalEnv }

-- | Parts of the environment that seldom change.
data SimplGlobalEnv
  = SimplGlobalEnv { sge_dflags   :: DynFlags
                   , sge_mode     :: SimplifierMode
                   , sge_ruleBase :: RuleBase
                   , sge_fams     :: (FamInstEnv, FamInstEnv) }

type SimplTermEnv = SimplEnv -- Environment where continuation bindings aren't relevant

newtype StaticEnv     = StaticEnv     SimplEnv -- Ignore dynamic-only part
newtype StaticTermEnv = StaticTermEnv SimplEnv -- Also ignore cont bindings

type SimplSubst env a = IdEnv (SubstAns env a) -- InId |--> SubstAns env a
data SubstAns env a
  = Done (Out a)
  | DoneId OutId
  | Susp env (In a)

type SimplIdSubst  = SimplSubst StaticTermEnv SeqCoreTerm
type SimplJvSubst  = SimplSubst StaticEnv     SeqCoreJoin
type TermSubstAns  = SubstAns   StaticTermEnv SeqCoreTerm
type JoinSubstAns  = SubstAns   StaticEnv     SeqCoreJoin
type KontSubst     = Maybe MetaKont

{-

Note [Metacontinuations]
------------------------

Sequent Core is a sequent calculus for call-by-name (lazy) evaluation. However,
much of GHC's optimization effort goes toward selectively applying call-by-value
(strict) rules instead whenever it is safe to do so. Since call-by-value has
different evaluation contexts from call-by-name, it has different continuations
as well. Hence, in order to support both call-by-name and call-by-value, the
simplifier's concept of a continuation must be made more general than Sequent
Core itself allows.

For instance, suppose that f is strict in its first argument, v is an arbitrary
term, and the simplifier is processing this command:

    < f | $ v; $ y; ret >

Say we have simplified f already, so we are now considering the strict argument
v. Typically, a sequent calculus expresses call-by-value argument evaluation
like so:

    < f | $ v; $ y; ret > --> < v | bind x. < f | $ x; $ y; ret > >

Here "bind x" means "bind the result to x and perform the following command."
In this case, we're saying to compute v, producing a value x, then plug x in as
the first argument to f.

Sequent Core is a restricted grammar, so we cannot actually form the command on
the right-hand side here. However, the simplifier state does not consist of a
command alone: We have both a command and an environment. Along with bindings
for terms, the environment carries a continuation. Hence the simplifier state is
actually something more like

    < f | $ v; $ y; ret > { k },

where "{ k }" indicates that k is the currently bound continuation. Then we can
write:

    < f | $ v; $ y; ret > { k } -->
    < v | ret > { bind x. < f | $ x; $ y; ret > { k } }

Now the expressions in braces are not restricted to be Sequent Core; they can
include syntax known only to the simplifier. So we say that the simplifier
state includes a *metacontinuation,* sometimes known as a *semantic
continuation.* The metacontinuation for a strict argument is exactly the
StrictArg form in the MetaKont datatype.

Note [StrictLet and StrictLamBind]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

GHC has just the one form of continuation, StrictBind, for either a strict let
or a strict beta-redex. It's not clear that there's any good way for us to
combine the two: StrictLet is used in simplCommand, which has a raw InCommand
as an argument, and StrictLamBind is used in simplTermInCommand, in which the
command has been split into frames and each has its scope attached. In order to
combine the two continuations, we would need a common entry point that could go
to either. We could always decompose the command argument to SimplCommand, but
attaching static environments to its frames hits one major snag: We don't know
the frames' static scope until after we've processed the let bindings! Absent
some serious knot-tying or datatype abuse, we just have to use two different
continuations.

-}

data MetaKont = SynKont { mk_frames :: [ScopedFrame]
                        , mk_end    :: ScopedEnd
                        , mk_dup    :: !DupFlag }
              | StrictArg { mk_argInfo :: ArgInfo
                          , mk_frames  :: [ScopedFrame]
                          , mk_end     :: ScopedEnd
                          , mk_context :: CallCtxt
                          , mk_dup     :: !DupFlag }
              | StrictLet { mk_env     :: StaticEnv
                          , mk_binder  :: InBndr
                          , mk_command :: InCommand } -- Never dupable
                                                      -- Note [Duplicating StrictBind] in GHC Simplify
              | StrictLamBind { mk_termEnv  :: StaticTermEnv
                              , mk_binder   :: InBndr
                              , mk_term     :: InTerm
                              , mk_coercion :: Maybe SubstedCoercion
                              , mk_frames   :: [ScopedFrame]
                              , mk_end      :: ScopedEnd 
                              , mk_context  :: CallCtxt } -- Never dupable

canDupMetaKont :: MetaKont -> Bool
canDupMetaKont mk
  = case mk of
      StrictLamBind {} -> False
      StrictLet {}     -> False
      _                -> mk_dup mk == OkToDup
                       

---------------------
-- Lexical scoping --
---------------------

{-

Note [Scoped values]
~~~~~~~~~~~~~~~~~~~~

A value of type Scoped t is a closure over t - that is, a t together with
information about the names bound in its lexical scope. It's useful to have
scoped types so that we can mix together objects from different scopes, even
some that have already been simplified.

A scoped value can be in two different states:

  - Incoming: This is a value that has not yet been seen by the simplifier. We
    need to keep around the environment under which it needs to be simplified.
  
  - Simplified: This is a value that has already been simplified. It may in
    addition be *duplicable*; mkDupableKont is in charge of putting things in
    the duplicable state. In either case, as term substitution has already been
    performed, most of the static environment is no longer needed.
    
One further wrinkle is metacontinuations (see Note [Metacontinuations]). Most of
the bindings carried in the environment can be substituted directly into a
Sequent Core expression, but a metacontinuation cannot in general. Hence even a
fully-simplified expression isn't necessarily "closed," and so a Simplified
value carries a Maybe MetaKont as its one remaining piece of context.

-}

-- TODO This is almost the same as SubstAns. Do we need both?
data Scoped env a = Incoming           env       (In  a)
                  | Simplified DupFlag KontSubst (Out a)
data DupFlag = NoDup | OkToDup
  deriving (Eq)

type ScopedFrame = Scoped StaticTermEnv SeqCoreFrame
type ScopedEnd   = Scoped StaticEnv SeqCoreEnd
type ScopedJoin  = Scoped StaticEnv SeqCoreJoin
type ScopedCommand = Scoped StaticEnv SeqCoreCommand

openScoped :: SimplEnvFragment env => SimplEnv -> Scoped env a -> (SimplEnv, In a)
openScoped env scoped
  = case scoped of
      Incoming     stat a -> (env `setEnvPart` stat, a)
      Simplified _ mk   a -> (zapSubstEnvs env `setKontSubst` mk, a)

unScope :: Scoped env a -> a
unScope scoped
  = case scoped of
      Incoming   _ a   -> a
      Simplified _ _ a -> a

okToDup :: Scoped env a -> Bool
okToDup (Simplified OkToDup _ _) = True
okToDup _                        = False

substScoped :: (SimplEnvFragment env, Substable a)
            => SimplEnv -> Scoped env a -> a
substScoped env scoped = case openScoped env scoped of (env', a) -> subst env' a

-----------------
-- Definitions --
-----------------

-- The original simplifier uses the IdDetails stored in a Var to store unfolding
-- info. We store similar data externally instead. (This is based on the Secrets
-- paper, section 6.3.) Note that we do update the unfoldings as well (see
-- setDef), but this requires translating expressions between Core and Sequent
-- Core; keeping our own data saves having to translate.
type IdDefEnv = IdEnv Definition
data Definition
  = NoDefinition
  | BoundToTerm { def_term :: OutTerm
                , def_src :: UnfoldingSource
                , def_level :: TopLevelFlag
                , def_guidance :: UnfoldingGuidance
                , def_arity :: Arity
                , def_isValue :: Bool
                , def_isConLike :: Bool
                , def_isWorkFree :: Bool
                , def_isExpandable :: Bool
                }
  | BoundToJoin { def_join :: OutJoin
                , def_src :: UnfoldingSource
                , def_guidance :: UnfoldingGuidance
                , def_arity :: Arity }
  | BoundToDFun { dfun_bndrs :: [OutVar]
                , dfun_dataCon :: DataCon
                , dfun_args :: [OutTerm] }
  | NotAmong [AltCon]

always :: UnfoldingGuidance
always = UnfWhen { ug_unsat_ok = True, ug_boring_ok = True }

mkTermDef :: SimplTermEnv -> TopLevelFlag -> OutTerm -> Definition
mkTermDef env level term
  = mkBoundToTerm env (dynFlags env) term InlineRhs level False

mkJoinDef :: SimplEnv -> OutJoin -> Definition
mkJoinDef env join
  = mkBoundToJoin env (dynFlags env) join InlineRhs

mkBoundToTerm :: SimplTermEnv -> DynFlags -> OutTerm -> UnfoldingSource -> TopLevelFlag
              -> Bool -> Definition
mkBoundToTerm env dflags term src level bottoming
  | isTopLevel level, bottoming, not (isTrivialTerm term)
  = NoDefinition
  | otherwise
  = mkBoundToTermWithGuidance env term src level arity guid
  where (arity, guid) = mkTermGuidance dflags term

mkBoundToJoin :: SimplTermEnv -> DynFlags -> OutJoin -> UnfoldingSource
              -> Definition
mkBoundToJoin env dflags join src
  = mkBoundToJoinWithGuidance env join src arity guid
  where (arity, guid) = mkJoinGuidance dflags join

mkBoundToTermWithGuidance :: SimplEnv -> OutTerm -> UnfoldingSource -> TopLevelFlag
                          -> Arity -> UnfoldingGuidance -> Definition
mkBoundToTermWithGuidance env term src level arity guid
  = BoundToTerm { def_term         = occurAnalyseTerm term
                , def_src          = src
                , def_level        = level
                , def_guidance     = guid
                , def_arity        = arity
                , def_isExpandable = termIsExpandable term
                , def_isValue      = termIsHNF env term
                , def_isWorkFree   = termIsWorkFree term
                , def_isConLike    = termIsConLike env term
                }

mkBoundToJoinWithGuidance :: SimplEnv -> OutJoin -> UnfoldingSource
                          -> Arity -> UnfoldingGuidance -> Definition
mkBoundToJoinWithGuidance _env join src arity guid
  = BoundToJoin { def_join         = occurAnalyseJoin join
                , def_src          = src
                , def_guidance     = guid
                , def_arity        = arity
                }

mkBoundToDFun :: [OutBndr] -> DataCon -> [OutArg] -> Definition
mkBoundToDFun bndrs con args = BoundToDFun { dfun_bndrs   = bndrs
                                           , dfun_dataCon = con
                                           , dfun_args    = map occurAnalyseTerm args }

termInlineBoringOk :: SeqCoreTerm -> Bool
joinInlineBoringOk :: SeqCoreJoin -> Bool
-- See Note [INLINE for small functions] in CoreUnfold
-- True => the result of inlining the expression is 
--         no bigger than the expression itself
--     eg      (\x y -> f y x)
-- This is a quick and dirty version. It doesn't attempt
-- to deal with  (\x y z -> x (y z))
-- The really important one is (x `cast` c)
(termInlineBoringOk, joinInlineBoringOk)
  = (\term -> nonNeg (goT 0 term), \join -> nonNeg (goJ join))
  where
    nonNeg Nothing  = False
    nonNeg (Just x) = x >= 0
    
    goT :: Int -> SeqCoreTerm -> Maybe Int
    goT credit (Lam x e) | isId x             = goT (credit+1) e
                         | otherwise          = goT credit e
    goT credit (Var {})                       = Just credit
    goT credit (Compute _ (Eval term fs Return))
                                              = goF credit fs >>= \credit' ->
                                                goT credit' term
    goT _      _                              = Nothing
    
    goF credit (App (Type {}) : fs)           = goF credit fs
    goF credit (App a : fs) | credit > 0  
                            , isTrivialTerm a = goF (credit-1) fs
    goF credit (Tick _ : fs)                  = goF credit fs -- dubious
    goF credit (Cast _ : fs) 		              = goF credit fs
    goF credit []                             = Just credit
    goF _      _                              = Nothing

    goJ (Join xs (Eval term fs Return))       = goF (length xs) fs >>= \credit' ->
                                                goT credit' term
    goJ _                                     = Nothing

mkTermGuidance :: DynFlags -> OutTerm -> (Arity, UnfoldingGuidance)
mkTermGuidance dflags term
  = (arity, guid)
  where
    arity = count isId bndrs
    guid  = guidanceForSize (isTrivialTerm term) arity size
    
    cap   = ufCreationThreshold dflags
    size  = termSize dflags cap term
    bndrs = fst (lambdas term)

mkJoinGuidance :: DynFlags -> OutJoin -> (Arity, UnfoldingGuidance)
mkJoinGuidance dflags join@(Join bndrs _)
  = (arity, guid)
  where
    arity = count isId bndrs
    guid  = guidanceForSize (isTrivialJoin join) arity size
    
    cap   = ufCreationThreshold dflags
    size  = joinSize dflags cap join

guidanceForSize :: Bool -> Int -> Maybe ExprSize -> UnfoldingGuidance
guidanceForSize _ _ Nothing = UnfNever
guidanceForSize triv arity (Just (ExprSize base args res))
  | uncondInline triv arity base = always
  | otherwise                    = UnfIfGoodArgs { ug_size = base
                                                 , ug_args = args
                                                 , ug_res  = res }

uncondInline :: Bool -> Arity -> Int -> Bool
-- Inline unconditionally if there no size increase
-- Size of call is arity (+1 for the function)
-- See GHC CoreUnfold: Note [INLINE for small functions]
uncondInline triv arity size 
  | arity > 0 = size <= 10 * (arity + 1)
  | otherwise = triv

------------------
-- In/Out Types --
------------------

type In a       = a
type InCommand  = SeqCoreCommand
type InTerm     = SeqCoreTerm
type InArg      = SeqCoreArg
type InKont     = SeqCoreKont
type InFrame    = SeqCoreFrame
type InEnd      = SeqCoreEnd
type InJoin     = SeqCoreJoin
type InAlt      = SeqCoreAlt
type InBind     = SeqCoreBind
type InBndr     = SeqCoreBndr
type InBindPair = SeqCoreBindPair
type InType     = Type
type InCoercion = Coercion
type InId       = Id
type InJoinId   = JoinId
type InVar      = Var
type InTyVar    = TyVar
type InCoVar    = CoVar

type Out a      = a
type OutCommand = SeqCoreCommand
type OutTerm    = SeqCoreTerm
type OutArg     = SeqCoreArg
type OutKont    = SeqCoreKont
type OutFrame   = SeqCoreFrame
type OutEnd     = SeqCoreEnd
type OutJoin    = SeqCoreJoin
type OutAlt     = SeqCoreAlt
type OutBind    = SeqCoreBind
type OutBndr    = SeqCoreBndr
type OutBindPair = SeqCoreBindPair
type OutType    = Type
type OutCoercion = Coercion
type OutId      = Id
type OutJoinId  = JoinId
type OutVar     = Var
type OutTyVar   = TyVar
type OutCoVar   = CoVar

-- Coercions have a third state, where substitution has been performed but not
-- optimization. (It is hoped that coercions are not so large that making
-- multiple passes like this is expensive.)
type SubstedCoercion = Coercion

-----------------
-- Environment --
-----------------

initialEnv :: DynFlags -> SimplifierMode -> RuleBase -> (FamInstEnv, FamInstEnv)
           -> SimplEnv
initialEnv dflags mode rules famEnvs
  = SimplEnv { se_idSubst = emptyVarEnv
             , se_jvSubst = emptyVarEnv
             , se_tvSubst = emptyVarEnv
             , se_cvSubst = emptyVarEnv
             , se_retTy   = Nothing
             , se_retKont = Nothing
             , se_context = BoringCtxt
             , se_inScope = emptyInScopeSet
             , se_defs    = emptyVarEnv
             , se_global  = initialGlobalEnv dflags mode rules famEnvs }
             
initialGlobalEnv :: DynFlags -> SimplifierMode -> RuleBase -> (FamInstEnv, FamInstEnv)
                 -> SimplGlobalEnv
initialGlobalEnv dflags mode rules famEnvs 
  = SimplGlobalEnv { sge_dflags   = dflags
                   , sge_mode     = mode
                   , sge_ruleBase = rules
                   , sge_fams     = famEnvs }

getMode :: SimplEnv -> SimplifierMode
getMode = sge_mode . se_global

updMode :: (SimplifierMode -> SimplifierMode) -> SimplEnv -> SimplEnv
updMode upd env@(SimplEnv { se_global = glob })
  = env { se_global = glob { sge_mode = upd (sge_mode glob) } }

dynFlags :: SimplEnv -> DynFlags
dynFlags = sge_dflags . se_global

getSimplRules :: SimplEnv -> RuleBase
getSimplRules = sge_ruleBase . se_global

getFamEnvs :: SimplEnv -> (FamInstEnv, FamInstEnv)
getFamEnvs = sge_fams . se_global

activeRule :: SimplEnv -> Activation -> Bool
-- Nothing => No rules at all
activeRule env
  | not (sm_rules mode) = \_ -> False     -- Rewriting is off
  | otherwise           = isActive (sm_phase mode)
  where
    mode = getMode env

getInScopeSet :: SimplEnv -> InScopeSet
getInScopeSet = se_inScope

enterScope :: SimplEnv -> InVar -> (SimplEnv, OutVar)
enterScope env x
  | isTyVar   x = enterTyVarScope env x
  | otherwise   = enterIdScope env x

enterKontScope :: SimplEnv -> CallCtxt -> InType -> (SimplEnv, OutType)
enterKontScope env ctxt ty
  = (env { se_jvSubst = emptyVarEnv
         , se_retTy   = Just ty'
         , se_retKont = Nothing
         , se_context = ctxt }, ty')
  where
    ty' = substTy env ty

enterScopes :: SimplEnv -> [InVar] -> (SimplEnv, [OutVar])
enterScopes = mapAccumL enterScope

enterRecScopes :: SimplEnv -> [InId] -> (SimplEnv, [OutId])
enterRecScopes = enterScopes

enterLamScope :: SimplEnv -> InVar -> (SimplEnv, OutVar)
enterLamScope env bndr
  | isId bndr && hasSomeUnfolding old_unf = seqId id2 `seq` (env2, id2) -- Special case
  | otherwise                             = enterScope env bndr         -- Normal case
  where
    old_unf = idUnfolding bndr
    (env1, id1) = enterIdScope env bndr
    id2  = id1 `setIdUnfolding` CoreSubst.substUnfolding (mkCoreSubst (text "enterLamScope") env) old_unf
    env2 = modifyInScope env1 id2

enterLamScopes :: SimplEnv -> [InVar] -> (SimplEnv, [OutVar])
enterLamScopes = mapAccumL enterLamScope

enterIdScope :: SimplEnv -> InId -> (SimplEnv, OutId)
enterIdScope env bndr
  | Coercion.isCoVar bndr = enterCoVarScope env bndr
  | otherwise             = enterNonCoVarIdScope env bndr
  
enterNonCoVarIdScope :: SimplEnv -> InId -> (SimplEnv, OutId)
enterNonCoVarIdScope env@(SimplEnv { se_inScope = in_scope, se_defs = defs
                                   , se_idSubst = id_subst, se_jvSubst = pv_subst })
                     old_id
  | tracing
  , new_id /= old_id
  , pprTrace "enterNonCoVarIdScope" (ppr old_id <+> darrow <+> ppr new_id) False
  = undefined
  | otherwise
  = (env { se_inScope = in_scope `extendInScopeSet` new_id,
           se_defs    = defs `delVarEnv` new_id,
           se_idSubst = new_id_subst,
           se_jvSubst = new_pv_subst }, new_id)
  where
    id1    = uniqAway in_scope old_id
    id2    = substIdType env id1
    new_id = zapFragileIdInfo id2       -- Zaps rules, worker-info, unfolding
                                        -- and fragile OccInfo

    is_pv  = isJoinId old_id
    
        -- Extend the substitution if the unique has changed,
        -- or there's some useful occurrence information
        -- See the notes with substTyVarBndr for the delSubstEnv
    new_id_subst | is_pv 
                 = id_subst
                 | new_id /= old_id
                 = extendVarEnv id_subst old_id (DoneId new_id)
                 | otherwise
                 = delVarEnv id_subst old_id
    new_pv_subst | not is_pv
                 = pv_subst
                 | new_id /= old_id
                 = extendVarEnv pv_subst old_id (DoneId new_id)
                 | otherwise
                 = delVarEnv pv_subst old_id

enterTyVarScope :: SimplEnv -> InTyVar -> (SimplEnv, OutTyVar)
enterTyVarScope env tv
  = case Type.substTyVarBndr (getTvSubst env) tv of
      (Type.TvSubst in_scope' tv_env', tv')
          | tracing
          , tv /= tv'
          , pprTrace "enterTyVarScope" (ppr tv <+> darrow <+> ppr tv') False
         -> undefined
          | otherwise
         -> (env { se_inScope = in_scope', se_tvSubst = tv_env' }, tv')

enterCoVarScope :: SimplEnv -> InCoVar -> (SimplEnv, OutCoVar)
enterCoVarScope env cv
  = case Coercion.substCoVarBndr (getCvSubst env) cv of
      (CvSubst in_scope' tv_env' cv_env', cv')
          | tracing
          , cv /= cv'
          , pprTrace "enterCoVarScope" (ppr cv <+> darrow <+> ppr cv') False
         -> undefined
          | otherwise
         -> (env { se_inScope = in_scope', se_tvSubst = tv_env', se_cvSubst = cv_env' }, cv')

mkFreshVar :: MonadUnique m => SimplEnv -> FastString -> Type -> m (SimplEnv, Var)
mkFreshVar env name ty
  = do
    x <- mkSysLocalM name ty
    let x'   = uniqAway (se_inScope env) x
        env' = env { se_inScope = extendInScopeSet (se_inScope env) x' }
    return (env', x')

---------------------------
-- Id-handling utilities --
---------------------------

seqId :: Id -> ()
seqId id = seqType (idType id)  `seq`
           idInfo id            `seq`
           ()
           
------------------
-- Substitution --
------------------

substId :: SimplEnv -> InId -> TermSubstAns
substId (SimplEnv { se_idSubst = ids, se_inScope = ins }) x
  = case lookupVarEnv ids x of
      -- See comments in GHC's SimplEnv.substId for explanations
      Nothing              -> DoneId (refine ins x)
      Just (DoneId x')     -> DoneId (refine ins x')
      Just (Done (Var x')) -> DoneId (refine ins x')
      Just ans             -> ans

substIdForId :: SimplEnv -> InId -> OutId
substIdForId env id
  = case substId env id of
      DoneId x' -> x'
      other     -> pprPanic "substIdForId" (ppr id <+> darrow <+> ppr other)

substPv :: SimplEnv -> InId -> JoinSubstAns
substPv (SimplEnv { se_jvSubst = pvs, se_inScope = ins }) j
  = case lookupVarEnv pvs j of
      Nothing                 -> DoneId (refine ins j)
      Just (DoneId j')        -> DoneId (refine ins j')
      Just ans                -> ans

substKv :: SimplEnv -> Maybe MetaKont
substKv = se_retKont

refine :: InScopeSet -> OutVar -> OutVar
refine ins x
  | isLocalId x
  = case lookupInScope ins x of
      Just x' -> x'
      Nothing -> pprTrace "refine" (text "variable not in scope:" <+> ppr x) x
  | otherwise
  = x

lookupRecBndr :: SimplEnv -> InId -> OutId
-- Look up an Id which has been put into the envt by enterRecScopes,
-- but where we have not yet done its RHS
lookupRecBndr (SimplEnv { se_inScope = in_scope, se_idSubst = ids, se_jvSubst = pvs }) v
  | isJoinId v
  = case lookupVarEnv pvs v of
      Just (DoneId v) -> v
      Just _ -> pprPanic "lookupRecBndr" (ppr v)
      Nothing -> refine in_scope v
  | otherwise
  = case lookupVarEnv ids v of
      Just (DoneId v) -> v
      Just _ -> pprPanic "lookupRecBndr" (ppr v)
      Nothing -> refine in_scope v

getTvSubst :: SimplEnv -> TvSubst
getTvSubst env = mkTvSubst (se_inScope env) (se_tvSubst env)

substTy :: SimplEnv -> Type -> Type
substTy env t = Type.substTy (getTvSubst env) t

substTyVar :: SimplEnv -> TyVar -> Type
substTyVar env tv = Type.substTyVar (getTvSubst env) tv

substIdType :: SimplEnv -> Var -> Var
substIdType env x
  | isEmptyVarEnv tvs || isEmptyVarSet (tyVarsOfType ty)
  = x
  | otherwise
  = x `setIdType` substTy env ty
  where
    tvs = se_tvSubst env
    ty = idType x

getCvSubst :: SimplEnv -> CvSubst
getCvSubst env = CvSubst (se_inScope env) (se_tvSubst env) (se_cvSubst env)

substCo :: SimplEnv -> Coercion -> Coercion
substCo env co = Coercion.substCo (getCvSubst env) co

substCoVar :: SimplEnv -> CoVar -> Coercion
substCoVar env co = Coercion.substCoVar (getCvSubst env) co

modifyInScope :: SimplEnv -> OutVar -> SimplEnv
modifyInScope env var = env { se_inScope = extendInScopeSet (se_inScope env) var }

addBndrRules :: SimplEnv -> InId -> OutId -> (SimplEnv, OutId)
addBndrRules env in_id out_id
  | isEmptySpecInfo old_rules = (env, out_id)
  | otherwise = (modifyInScope env final_id, final_id)
  where
    subst     = mkCoreSubst (text "local rules") env
    old_rules = idSpecialisation in_id
    new_rules = CoreSubst.substSpec subst out_id old_rules
    final_id  = out_id `setIdSpecialisation` new_rules

-- Convert a whole environment to a CoreSubst.Subst. A fairly desperate measure.
mkCoreSubst :: SDoc -> SimplEnv -> CoreSubst.Subst
mkCoreSubst doc env@(SimplEnv { se_inScope = in_scope, se_tvSubst = tv_env, se_cvSubst = cv_env
                              , se_idSubst = id_env, se_jvSubst = pv_env })
  = mk_subst tv_env cv_env id_env pv_env
  where
    mk_subst tv_env cv_env id_env pv_env = CoreSubst.mkSubst (mapInScopeSet fiddleJoinVar in_scope)
                                             tv_env cv_env
                                             (mapVarEnv fiddle id_env `plusVarEnv`
                                              mapVarEnv fiddleJoin pv_env)

    fiddle (Done e)          = termToCoreExpr e
    fiddle (DoneId v)        = Core.Var v
    fiddle (Susp (StaticTermEnv env') e) = termToCoreExpr (substTerm (text "mkCoreSubst" <+> doc) env' e)
                                                -- Don't shortcut here
                                                
    fiddleJoinVar x | isJoinId x = joinIdToCore retTy x
                    | otherwise  = x
    
    fiddleJoin (Done pk)    = joinToCoreExpr (retType env) pk
    fiddleJoin (DoneId j)   = Core.Var (joinIdToCore retTy j)
    fiddleJoin (Susp (StaticEnv env') e) = joinToCoreExpr retTy (substJoin (text "mkCoreSubst" <+> doc) env' e)
    
    mapInScopeSet :: (Var -> Var) -> InScopeSet -> InScopeSet
    mapInScopeSet f = mkInScopeSet . mapVarEnv f . getInScopeVars
    
    retTy = retType env

substTerm    :: SDoc -> SimplEnv -> SeqCoreTerm    -> SeqCoreTerm
substKont    :: SDoc -> SimplEnv -> SeqCoreKont    -> SeqCoreKont
substFrame   :: SDoc -> SimplEnv -> SeqCoreFrame   -> SeqCoreFrame
substEnd     :: SDoc -> SimplEnv -> SeqCoreEnd     -> SeqCoreEnd
substJoin    :: SDoc -> SimplEnv -> SeqCoreJoin    -> SeqCoreJoin
substCommand :: SDoc -> SimplEnv -> SeqCoreCommand -> SeqCoreCommand

substTerm _doc env term    = doSubstT env term
substKont _doc env kont    = doSubstK env kont
substFrame _doc env frame  = doSubstF env frame
substEnd _doc env end      = doSubstE env end
substJoin _doc env pk      = doSubstJ env pk
substCommand _doc env comm = doSubstC env comm

doSubstT :: SimplEnv -> SeqCoreTerm -> SeqCoreTerm
doSubstT env (Var x)
  = case substId env x of
      DoneId x' -> Var x'
      Done term -> term
      Susp stat term -> doSubstT (stat `inDynamicScopeForTerm` env) term
doSubstT env (Type ty)
  = Type (substTy env ty)
doSubstT env (Coercion co)
  = Coercion (substCo env co)
doSubstT _ (Lit lit)
  = Lit lit
doSubstT env (Lam bndr body)
  = Lam bndr' (doSubstT env' body)
  where (env', bndr') = enterScope env bndr
doSubstT env (Compute ty comm)
  = Compute ty' (doSubstC env' comm)
  where
    (env', ty') = enterKontScope env BoringCtxt ty

doSubstK :: SimplEnv -> SeqCoreKont -> SeqCoreKont
doSubstK env (fs, end)
  = (map (doSubstF env) fs, doSubstE env end)

doSubstF :: SimplEnv -> SeqCoreFrame -> SeqCoreFrame
doSubstF env (App arg)
  = App (doSubstT env arg)
doSubstF env (Cast co)
  = Cast (substCo env co)
doSubstF env (Tick (Breakpoint n ids))
  = Tick (Breakpoint n (map (substIdForId env) ids))
doSubstF _ (Tick ti)
  = Tick ti

doSubstE :: SimplEnv -> SeqCoreEnd -> SeqCoreEnd
doSubstE _ Return = Return
doSubstE env (Case x alts)
  = Case x' alts'
  where
    (env', x') = enterScope env x
    alts' = map doAlt alts
    doAlt (Alt ac bndrs rhs)
      = let (env'', bndrs') = enterScopes env' bndrs
            rhs' = doSubstC env'' rhs
        in Alt ac bndrs' rhs'

doSubstJ :: SimplEnv -> SeqCoreJoin -> SeqCoreJoin
doSubstJ env (Join bndrs comm) = Join bndrs' (doSubstC env' comm)
  where (env', bndrs') = enterLamScopes env bndrs

doSubstC :: SimplEnv -> SeqCoreCommand -> SeqCoreCommand
doSubstC env (Let bind body)
  = Let bind' (doSubstC env' body)
  where (env', bind') = doSubstB env bind
doSubstC env (Jump args j)
  = case substPv env j of
      DoneId j' -> Jump args' j'
      Done (Join bndrs body) -> doSubstC env' body
        where
          env' = foldl extend (zapSubstEnvs env) (bndrs `zip` args')
      Susp stat (Join bndrs body) -> doSubstC env' body
        where
          env' = foldl extend (stat `inDynamicScope` env) (bndrs `zip` args')
  where
    args' = map (doSubstT env) args
    extend env (bndr, arg) = extendIdSubst env bndr (Done arg)
doSubstC env (Eval v fs e)
  = Eval (doSubstT env v) (doSubstF env <$> fs) (doSubstE env e)
    
doSubstB :: SimplEnv -> SeqCoreBind -> (SimplEnv, SeqCoreBind)
doSubstB env bind
  = case bind of
      NonRec pair -> (env', NonRec pair')
        where
          bndr = binderOfPair pair
          (env', bndr') = enterScope env bndr
          pair' = doRhs env bndr' pair
      Rec pairs -> (env', Rec pairs')
        where
          bndrs = map binderOfPair pairs
          (env', bndrs') = enterRecScopes env bndrs
          pairs' = zipWith (doRhs env') bndrs' pairs
  where
    doRhs env' bndr' (BindTerm _ term) = BindTerm bndr' (doSubstT env' term)
    doRhs env' bndr' (BindJoin _ join) = BindJoin bndr' (doSubstJ env' join)

class Substable a where
  subst :: SimplEnv -> a -> a

instance Substable SeqCoreTerm where subst = doSubstT
instance Substable SeqCoreKont where subst = doSubstK
instance Substable SeqCoreFrame where subst = doSubstF
instance Substable SeqCoreEnd where subst = doSubstE
instance Substable SeqCoreJoin where subst = doSubstJ
instance Substable SeqCoreCommand where subst = doSubstC

extendIdSubst :: SimplEnv -> InVar -> TermSubstAns -> SimplEnv
extendIdSubst env x rhs
  = env { se_idSubst = extendVarEnv (se_idSubst env) x rhs }

extendJvSubst :: SimplEnv -> InVar -> JoinSubstAns -> SimplEnv
extendJvSubst env x rhs
  = env { se_jvSubst = extendVarEnv (se_jvSubst env) x rhs }

extendSubstWithInBindPair :: SimplEnv -> StaticEnv -> InBindPair -> SimplEnv
extendSubstWithInBindPair env stat pair
  = case pair of
      BindTerm x term -> extendIdSubst env x (Susp (narrowToStaticTermPart stat) term)
      BindJoin j join -> extendJvSubst env j (Susp stat join)

extendSubstWithOutBindPair :: SimplEnv -> OutBindPair -> SimplEnv
extendSubstWithOutBindPair env pair
  = case pair of
      BindTerm x (Var x') -> extendIdSubst env x (DoneId x')
      BindTerm x term     -> extendIdSubst env x (Done term)
      BindJoin j join     -> extendJvSubst env j (Done join)

extendTvSubst :: SimplEnv -> InTyVar -> OutType -> SimplEnv
extendTvSubst env@(SimplEnv { se_tvSubst = tvs }) tyVar ty
  = env { se_tvSubst = extendVarEnv tvs tyVar ty }

extendCvSubst :: SimplEnv -> InCoVar -> OutCoercion -> SimplEnv
extendCvSubst env@(SimplEnv { se_cvSubst = cvs }) coVar co
  = env { se_cvSubst = extendVarEnv cvs coVar co }

setRetKont :: SimplEnv -> MetaKont -> SimplEnv
setRetKont env mk
  = env { se_retKont = Just mk }

setKontSubst :: SimplEnv -> KontSubst -> SimplEnv
setKontSubst env mk_m
  = env { se_retKont = mk_m }

pushKont :: SimplEnv -> InKont -> SimplEnv
pushKont env (frames, end)
  -- Since invoking this metacontinuation will restore the current environment,
  -- the original metacontinuation will run after this one.
  = env `setRetKont` SynKont { mk_frames = Incoming (termStaticPart env) <$> frames
                             , mk_end    = Incoming (staticPart env) end
                             , mk_dup    = NoDup }

zapSubstEnvs :: SimplEnv -> SimplEnv
zapSubstEnvs env
  = env { se_idSubst = emptyVarEnv
        , se_jvSubst = emptyVarEnv
        , se_tvSubst = emptyVarEnv
        , se_cvSubst = emptyVarEnv
        , se_retKont = Nothing }

zapKontSubstEnvs :: SimplEnv -> SimplTermEnv
zapKontSubstEnvs env
  = env { se_jvSubst = emptyVarEnv
        , se_retKont = Nothing }

zapKontSubstEnvsStatic :: StaticEnv -> StaticTermEnv
zapKontSubstEnvsStatic (StaticEnv env)
  = StaticTermEnv (zapKontSubstEnvs env)

setSubstEnvs :: SimplEnv -> [OutBindPair] -> SimplEnv
setSubstEnvs env pairs
  = env { se_idSubst = mkVarEnv [ (id, Done term)  | BindTerm id term          <- pairs, isId id ]
        , se_jvSubst = mkVarEnv [ (id, Done join)  | BindJoin id join          <- pairs ]
        , se_tvSubst = mkVarEnv [ (tv, ty)         | BindTerm tv (Type ty)     <- pairs ]
        , se_cvSubst = mkVarEnv [ (cv, co)         | BindTerm cv (Coercion co) <- pairs ]
        , se_retKont = Nothing }

retType :: SimplEnv -> Type
retType env
  | Just ty <- se_retTy env
  = substTy env ty
  | otherwise
  = panic "retType at top level"

getContext :: SimplEnv -> CallCtxt
getContext = se_context

-- FIXME Getter/setter pair gives off code smell. Setting the call context
-- should probably be synchronous with entering or exiting a Compute.
setContext :: SimplEnv -> CallCtxt -> SimplEnv
setContext env ctxt = env { se_context = ctxt }

---------------------------
-- Environment fragments --
---------------------------

-- | Extract the part of the environment relating to lexical scope, such as
-- substitutions being performed. These are the values that need to be stored
-- in any kind of closure. What's *not* included is data that might change
-- between when a binding is first encountered and where it's actually
-- processed; in particular, there may be more variables in scope or they may
-- have different states (because we have gone into a Case on a variable, say).
--
-- The only use for a StaticEnv is to attach it to a SimplEnv that provides
-- information about the dynamic context; see 'setStaticPart' and
-- 'inDynamicScope'.
staticPart :: SimplEnv -> StaticEnv
staticPart = StaticEnv

-- | Like 'staticPart', but also leave out information about bound continuations
-- (both join points and the "ret" continuation). Appropriate for closing values
-- that are "continuation-closed", like terms and frames, and hence cannot have
-- free occurrences of continuation variables.
termStaticPart :: SimplEnv -> StaticTermEnv
termStaticPart = StaticTermEnv

narrowToStaticTermPart :: StaticEnv -> StaticTermEnv
narrowToStaticTermPart (StaticEnv env) = StaticTermEnv env

setStaticPart :: SimplEnv -> StaticEnv -> SimplEnv
setStaticPart dest (StaticEnv !src)
  = dest { se_idSubst = se_idSubst src
         , se_tvSubst = se_tvSubst src
         , se_cvSubst = se_cvSubst src
         , se_jvSubst = se_jvSubst src
         , se_retKont = se_retKont src
         , se_retTy   = se_retTy   src }

setStaticTermPart :: SimplEnv -> StaticTermEnv -> SimplTermEnv
setStaticTermPart dest (StaticTermEnv !src)
  = dest { se_idSubst = se_idSubst src
         , se_tvSubst = se_tvSubst src
         , se_cvSubst = se_cvSubst src
         , se_jvSubst = emptyVarEnv 
         , se_retKont = Nothing
         , se_retTy   = Nothing }

inDynamicScope :: StaticEnv -> SimplEnv -> SimplEnv
inDynamicScope = flip setStaticPart

inDynamicScopeForTerm :: StaticTermEnv -> SimplEnv -> SimplTermEnv
inDynamicScopeForTerm = flip setStaticTermPart

class SimplEnvFragment a where
  envPart :: SimplEnv -> a
  setEnvPart :: SimplEnv -> a -> SimplEnv

instance SimplEnvFragment StaticEnv where
  envPart = staticPart
  setEnvPart = setStaticPart

instance SimplEnvFragment StaticTermEnv where
  envPart = termStaticPart
  setEnvPart = setStaticTermPart

emptyStaticEnv :: StaticEnv
emptyStaticEnv
  = StaticEnv $ SimplEnv { se_idSubst = emptyVarEnv
                         , se_tvSubst = emptyVarEnv
                         , se_cvSubst = emptyVarEnv
                         , se_jvSubst = emptyVarEnv
                         , se_retKont = Nothing
                         , se_context = na
                         , se_inScope = na
                         , se_retTy   = na
                         , se_defs    = na
                         , se_global  = na }
  where na = panic "emptyStaticEnv"

emptyStaticTermEnv :: StaticTermEnv
emptyStaticTermEnv
  = StaticTermEnv $ SimplEnv { se_idSubst = emptyVarEnv
                             , se_tvSubst = emptyVarEnv
                             , se_cvSubst = emptyVarEnv
                             , se_jvSubst = na
                             , se_retKont = na
                             , se_context = na
                             , se_inScope = na
                             , se_retTy   = na
                             , se_defs    = na
                             , se_global  = na }
  where na = panic "emptyStaticTermEnv"

------------
-- Floats --
------------

-- See [Simplifier floats] in SimplEnv

data Floats = Floats (OrdList OutBind) FloatFlag

data FloatFlag
  = FltLifted   -- All bindings are lifted and lazy
                --  Hence ok to float to top level, or recursive

  | FltOkSpec   -- All bindings are FltLifted *or*
                --      strict (perhaps because unlifted,
                --      perhaps because of a strict binder),
                --        *and* ok-for-speculation
                --  Hence ok to float out of the RHS
                --  of a lazy non-recursive let binding
                --  (but not to top level, or into a rec group)

  | FltCareful  -- At least one binding is strict (or unlifted)
                --      and not guaranteed cheap
                --      Do not float these bindings out of a lazy let

andFF :: FloatFlag -> FloatFlag -> FloatFlag
andFF FltCareful _          = FltCareful
andFF FltOkSpec  FltCareful = FltCareful
andFF FltOkSpec  _          = FltOkSpec
andFF FltLifted  flt        = flt

allFF :: [FloatFlag] -> FloatFlag
allFF = foldr andFF FltLifted

classifyFF :: SeqCoreBind -> FloatFlag
classifyFF (NonRec (BindTerm bndr rhs))
  | not (isStrictId bndr)    = FltLifted
  | termOkForSpeculation rhs = FltOkSpec
  | otherwise                = FltCareful
classifyFF _ = FltLifted

doFloatFromRhs :: TopLevelFlag -> RecFlag -> Bool -> OutTerm -> Floats -> Bool
-- If you change this function look also at FloatIn.noFloatFromRhs
doFloatFromRhs lvl rc str rhs (Floats fs ff)
  =  not (isNilOL fs) && want_to_float && can_float
  where
     want_to_float = isTopLevel lvl || termIsCheap rhs || termIsExpandable rhs 
                     -- See Note [Float when cheap or expandable]
     can_float = case ff of
                   FltLifted  -> True
                   FltOkSpec  -> isNotTopLevel lvl && isNonRec rc
                   FltCareful -> isNotTopLevel lvl && isNonRec rc && str

emptyFloats :: Floats
emptyFloats = Floats nilOL FltLifted

unitFloat :: OutBind -> Floats
unitFloat bind = Floats (unitOL bind) (classifyFF bind)

addNonRecFloat :: SimplEnv -> OutBindPair -> (Floats, SimplEnv)
addNonRecFloat env pair
  = id `seq`   -- This seq forces the Id, and hence its IdInfo,
               -- and hence any inner substitutions
    (flts, env `augmentFromFloats` flts)
  where
    flts = unitFloat (NonRec pair)
    id = binderOfPair pair

mapBinds :: Functor f => (BindPair b -> BindPair b) -> f (Bind b) -> f (Bind b)
mapBinds f pairs = fmap app pairs
  where 
    app (NonRec pair) = NonRec (f pair)
    app (Rec pair)    = Rec (map f pair)

mapFloats :: (OutBindPair -> OutBindPair) -> Floats -> Floats
mapFloats fun (Floats fs ff)
   = Floats (mapBinds fun fs) ff

extendFloats :: OutBind -> Floats -> Floats
-- Add these bindings to the floats
extendFloats bind flts
  = flts `addFloats` unitFloat bind

augmentFromFloats :: SimplEnv -> Floats -> SimplEnv
-- Add the floats to the environment's in-scope set
-- We might want to add to se_defs as well, but those are inessential (we can
-- recover the same information from the translated unfolding) and we would have
-- to carry around Definitions along with Floats.
augmentFromFloats env (Floats fs _)
  | isNilOL fs
  = env
  | otherwise
  = env { se_inScope = extendInScopeSetList (se_inScope env) bndrs }
  where
    bndrs = bindersOfBinds (fromOL fs)

wrapBind :: SeqCoreBind -> SeqCoreCommand -> SeqCoreCommand
wrapBind bind@(Rec {}) cmd = Let bind cmd
wrapBind (NonRec pair) cmd = addNonRec pair cmd

wrapFloats, wrapKontFloats :: Floats -> OutCommand -> OutCommand
wrapFloats flts cmd = foldrOL wrapBind cmd (floatBinds flts)

wrapKontFloats flts cmd
  = foldr wrapBind cmd (mapMaybe onlyKonts binds)
  where
    binds = fromOL (floatBinds flts)
    onlyKonts bind@(NonRec pair) | bindsJoin pair = Just bind
                                 | otherwise      = Nothing
    onlyKonts (Rec pairs)        | let pairs' = filter bindsJoin pairs
                                 , not (null pairs')
                                 = Just (Rec pairs')
                                 | otherwise
                                 = Nothing


{-
Note [Wrap around compute]
~~~~~~~~~~~~~~~~~~~~~~~~~~

Suppose we have floats F and we wrap around a term (compute p. c), that is, we
calculate

F[compute p. c].

Remembering that terms are continuation-closed, we know two things:

1. Any continuations let-bound in F will be dead bindings, and
2. Any terms bound in F can float into c.

We are safe, then, in saying

F[compute p. c] = compute p. F'[c],

where F' contains only the term bindings from F. Of course, if a binding *is*
trying to float up past a compute, something has gone very wrong, so we check
for this condition and warn.
-}

wrapFloatsAroundTerm :: Floats -> OutTerm -> OutTerm
wrapFloatsAroundTerm flts term
  | isEmptyFloats flts
  = term
wrapFloatsAroundTerm flts (Compute p comm)
  -- See Note [Wrap around compute]
  = warnPprTrace (not $ hasNoKontFloats flts) __FILE__ __LINE__
      (text "cont floats escaping body of command:" <+> ppr comm $$
       text "floats:" <+> brackets (pprWithCommas (ppr . bindersOf)
                                                  (getFloatBinds flts))) $
    Compute p (wrapFloats (zapKontFloats flts) comm)
wrapFloatsAroundTerm flts term
  = mkCompute (termType term) $ wrapFloats flts (mkCommand [] term [] Return)

addFloats :: Floats -> Floats -> Floats
addFloats (Floats bs1 l1) (Floats bs2 l2)
  = Floats (bs1 `appOL` bs2) (l1 `andFF` l2)

catFloats :: [Floats] -> Floats
catFloats fltss = Floats (concatOL [ fs | Floats fs _ <- fltss ])
                         (allFF    [ ff | Floats _ ff <- fltss ])

addingFloats :: Monad m => Floats -> m (Floats, a) -> m (Floats, a)
addingFloats flts m | isEmptyFloats flts = m
                    | otherwise          = do (flts', ans) <- m
                                              return (flts `addFloats` flts', ans)

zapKontFloats :: Floats -> Floats
zapKontFloats (Floats fs ff)
  = Floats fs' ff
  where
    fs' = toOL . mapMaybe removeKonts . fromOL $ fs
    removeKonts (Rec pairs) | not (null pairs') = Just (Rec pairs')
                            where pairs'        = filter bindsTerm pairs
    removeKonts bind@(NonRec (BindTerm {}))     = Just bind
    removeKonts _                               = Nothing

addRecFloats :: SimplEnv -> Floats -> (Floats, SimplEnv)
-- This is all very specific to the way recursive bindings are
-- handled; see Simpl.simplRecBind
addRecFloats env (Floats bs ff)
  = assert (case ff of { FltLifted -> True; _ -> False })
  $ (flt, env `augmentFromFloats` flt)
  where
    flt = unitFloat (Rec (flattenBinds (fromOL bs)))

getFloatBinds :: Floats -> [OutBind]
getFloatBinds = fromOL . floatBinds

floatBinds :: Floats -> OrdList OutBind
floatBinds (Floats bs _) = bs

isEmptyFloats :: Floats -> Bool
isEmptyFloats = isNilOL . floatBinds

hasNoKontFloats :: Floats -> Bool
hasNoKontFloats = foldrOL (&&) True . mapOL (all bindsTerm . flattenBind)
                                    . floatBinds

-----------------------------
-- Definitions (continued) --
-----------------------------

findDefBy :: SimplEnv -> OutId -> (Id -> Unfolding) -> Definition
findDefBy env var id_unf
  | isStrongLoopBreaker (idOccInfo var)
  = NoDefinition
  | otherwise
  = lookupVarEnv (se_defs env) var `orElse` unfoldingToDef var (id_unf var)

findDef :: SimplEnv -> OutId -> Definition
findDef env var
  = findDefBy env var idUnfolding

findRealDef :: SimplEnv -> OutId -> Definition
findRealDef env var
  = lookupVarEnv (se_defs env) var `orElse` unfoldingToDef var (realIdUnfolding var)

expandTermDef_maybe :: Definition -> Maybe SeqCoreTerm
expandTermDef_maybe (BoundToTerm { def_isExpandable = True, def_term = term }) = Just term
expandTermDef_maybe def@(BoundToJoin {}) = pprPanic "expandTermDef_maybe" (ppr def)
expandTermDef_maybe _ = Nothing

getUnfoldingInRuleMatch :: SimplEnv -> (Id -> Unfolding)
-- When matching in RULE, we want to "look through" an unfolding
-- (to see a constructor) if *rules* are on, even if *inlinings*
-- are not.  A notable example is DFuns, which really we want to
-- match in rules like (op dfun) in gentle mode. Another example
-- is 'otherwise' which we want exprIsConApp_maybe to be able to
-- see very early on
getUnfoldingInRuleMatch env
  = id_unf
  where
    mode = getMode env
    id_unf id | unf_is_active id = idUnfolding id
              | otherwise        = NoUnfolding
    unf_is_active id
     | not (sm_rules mode) = active_unfolding_minimal id
     | otherwise           = isActive (sm_phase mode) (idInlineActivation id)

unfoldingToDef :: Var -> Unfolding -> Definition
unfoldingToDef var _ | isJoinId var = NoDefinition -- Can't translate a join in isolation
unfoldingToDef _ NoUnfolding     = NoDefinition
unfoldingToDef _ (OtherCon cons) = NotAmong cons
unfoldingToDef _ unf@(CoreUnfolding {})
  = BoundToTerm { def_term         = termFromCoreExpr (uf_tmpl unf)
                , def_src          = uf_src unf
                , def_level        = if uf_is_top unf then TopLevel else NotTopLevel
                , def_guidance     = uf_guidance unf
                , def_arity        = uf_arity unf
                , def_isValue      = uf_is_value unf
                , def_isConLike    = uf_is_conlike unf
                , def_isWorkFree   = uf_is_work_free unf
                , def_isExpandable = uf_expandable unf }
unfoldingToDef _ unf@(DFunUnfolding {})
  = BoundToDFun { dfun_bndrs    = df_bndrs unf
                , dfun_dataCon  = df_con unf
                , dfun_args     = map (occurAnalyseTerm . termFromCoreExpr)
                                      (df_args unf) }

setDef :: SimplEnv -> OutId -> Definition -> (SimplEnv, OutId)
setDef env x def
  = (env', x')
  where
    env' = env { se_inScope = extendInScopeSet (se_inScope env) x'
               , se_defs    = extendVarEnv (se_defs env) x' def }
    x'   = x `setIdUnfolding` defToUnfolding def

defToUnfolding :: Definition -> Unfolding
defToUnfolding NoDefinition    = NoUnfolding
defToUnfolding (NotAmong cons) = mkOtherCon cons
defToUnfolding (BoundToJoin { def_join = _join })
  = NoUnfolding -- TODO Can we do better? Translating requires knowing the outer linear cont.
defToUnfolding (BoundToTerm { def_src = src, def_term = term, def_level = lev, def_guidance = guid })
  = mkCoreUnfolding src (isTopLevel lev) (termToCoreExpr term)
      (termArity term) guid
defToUnfolding (BoundToDFun { dfun_bndrs = bndrs, dfun_dataCon = con, dfun_args = args})
  = mkDFunUnfolding bndrs con (map termToCoreExpr args)

-- TODO This might be in Syntax, but since we're not storing our "unfoldings" in
-- ids, we rely on the environment to tell us whether a variable has been
-- evaluated.

termIsHNF, termIsConLike :: SimplEnv -> SeqCoreTerm -> Bool
termIsHNF     env = termIsHNFLike isDataConWorkId defIsEvald env
termIsConLike env = termIsHNFLike isConLikeId defIsConLike env

termIsHNFLike :: (Var -> Bool) -> (Definition -> Bool) -> SimplEnv -> SeqCoreTerm -> Bool
termIsHNFLike isCon isHNFDef env term
  = isHNFLike term []
  where
    isHNFLike _                fs | hasTick fs = False
    isHNFLike (Var id)         fs = isCon id
                                 || isHNFDef (findDef env id)
                                 || idArity id > count isRuntimeApp fs
    isHNFLike (Lit {})         _  = True
    isHNFLike (Coercion {})    _  = True
    isHNFLike (Type {})        _  = True
    isHNFLike (Lam x body)     fs = isId x || isHNFLike body fs
    isHNFLike (Compute _ comm) _  = isHNFLikeComm comm
    
    isHNFLikeComm (Let _ comm)  = isHNFLikeComm comm
    isHNFLikeComm (Jump _ j)    = isCon j -- emphasis on constructor-*like*
    isHNFLikeComm (Eval v fs Return) = isHNFLike v fs
    isHNFLikeComm _             = False
    
    isRuntimeApp (App (Type _)) = False
    isRuntimeApp (App _)        = True
    isRuntimeApp _              = False
    
    hasTick fs = or [ tickishCounts ti | Tick ti <- fs ]

defIsEvald :: Definition -> Bool
defIsEvald (NotAmong _) = True
defIsEvald (BoundToTerm { def_isValue = vl }) = vl
defIsEvald (BoundToJoin {}) = True
defIsEvald _ = False

defIsConLike :: Definition -> Bool
defIsConLike (NotAmong _) = True
defIsConLike (BoundToTerm { def_isConLike = cl }) = cl
defIsConLike (BoundToJoin {}) = True
defIsConLike _ = False

defIsCheap :: Definition -> Bool
defIsCheap (BoundToTerm { def_isWorkFree = wf }) = wf
defIsCheap (BoundToJoin {}) = True
defIsCheap _ = False

defIsStable :: Definition -> Bool
defIsStable (BoundToTerm { def_src = src })  = isStableSource src
defIsStable (BoundToJoin { def_src = src })  = isStableSource src
defIsStable (BoundToDFun {})                 = True
defIsStable _                                = False

defGuidance :: Definition -> Maybe UnfoldingGuidance
defGuidance (BoundToTerm { def_guidance = guid }) = Just guid
defGuidance (BoundToJoin { def_guidance = guid }) = Just guid
defGuidance _                                     = Nothing

defIsSmallEnoughToInline :: DynFlags -> Definition -> Bool
defIsSmallEnoughToInline dflags def
  = case defGuidance def of
      Just (UnfIfGoodArgs { ug_size = size }) -> size <= ufUseThreshold dflags
      _                                       -> False

activeUnfolding :: SimplEnv -> Id -> Bool
activeUnfolding env
  | not (sm_inline mode) = active_unfolding_minimal
  | otherwise            = case sm_phase mode of
                             InitialPhase -> active_unfolding_gentle
                             Phase n      -> active_unfolding n
  where
    mode = getMode env

active_unfolding_minimal :: Id -> Bool
-- Compuslory unfoldings only
-- Ignore SimplGently, because we want to inline regardless;
-- the Id has no top-level binding at all
--
-- NB: we used to have a second exception, for data con wrappers.
-- On the grounds that we use gentle mode for rule LHSs, and
-- they match better when data con wrappers are inlined.
-- But that only really applies to the trivial wrappers (like (:)),
-- and they are now constructed as Compulsory unfoldings (in MkId)
-- so they'll happen anyway.
active_unfolding_minimal id = isCompulsoryUnfolding (realIdUnfolding id)

active_unfolding :: PhaseNum -> Id -> Bool
active_unfolding n id = isActiveIn n (idInlineActivation id)

active_unfolding_gentle :: Id -> Bool
-- Anything that is early-active
-- See Note [Gentle mode]
active_unfolding_gentle id
  =  isInlinePragma prag
  && isEarlyActive (inlinePragmaActivation prag)
       -- NB: wrappers are not early-active
  where
    prag = idInlinePragma id

termIsConApp_maybe :: SimplEnv -> (Id -> Unfolding) -> OutTerm -> Maybe (DataCon, [OutType], [OutTerm])
termIsConApp_maybe env id_unf term
  -- Proceed basically like Simplify.exprIsConApp_maybe, only use the whole
  -- environment rather than a more compact Subst type, since we don't (yet)
  -- have a Subst for sequent core
  = goT (Left (se_inScope env)) term
  where
    goT :: Either InScopeSet SimplEnv -> OutTerm
        -> Maybe (DataCon, [OutType], [OutTerm])
    goT subst (Compute _ (Eval v fs Return)) = go subst v fs Nothing
    goT _     (Compute _ _) = Nothing
    goT subst v             = go subst v [] Nothing
    
    go :: Either InScopeSet SimplEnv -> OutTerm -> [OutFrame]
       -> Maybe OutCoercion
       -> Maybe (DataCon, [Type], [OutTerm])
    go subst term@(Lam {}) fs co_m
      | Just (args, co_m') <- extractArgs subst True fs -- only trivial args
      , let (bndrs, body) = lambdas term
      , bndrs `equalLength` args
      , Just (term', fs') <- match body
      = let subst' = foldl2 extend subst bndrs args
            co_m'' = mkTransCoMaybe co_m co_m'
        in go subst' term' (map (subst_frame subst') fs') co_m''
      where
        match (Compute _ (Eval term fs Return))
                            = Just (term, fs)
        match (Compute _ _) = Nothing
        match other         = Just (other, [])
    
    go subst (Compute _ (Eval term fs' Return)) fs co_m
      = go subst term (fs' ++ fs) co_m
    
    go (Right env') (Var x) fs co_m
       = go (Left (se_inScope env')) value fs co_m
       where
         value = case substId env' x of
                   DoneId x'  -> Var x'
                   Done value -> value
                   Susp {}    -> pprPanic "termIsConApp_maybe::goT"
                                          (text "suspended ans for" <+> ppr x)
    
    go (Left ins) (Var fun) fs co_m
      | Just dc <- isDataConWorkId_maybe fun
      , Just (args, co_m') <- extractArgs (Left ins) False fs
      , count isValueArg args == idArity fun
      = dealWithCoercion (mkTransCoMaybe co_m co_m') dc args
      | BoundToDFun { dfun_bndrs = bndrs
                    , dfun_dataCon = dc
                    , dfun_args = dcArgs } <- def
      , Just (args, co_m') <- extractArgs (Left ins) False fs
      , bndrs `equalLength` args
      = let env   = env0 { se_inScope = ins } `setSubstEnvs` zipWith BindTerm bndrs args
            args' = map (substTerm (text "termIsConApp_maybe::go") env) dcArgs
        in dealWithCoercion (mkTransCoMaybe co_m co_m') dc args'
      | assert (not (isJoinId fun)) True
      , Just term <- expandTermDef_maybe def
      , def_arity def == 0
      = let ins' = extendInScopeSetSet ins (termFreeVars term)
        in go (Left ins') term fs co_m
      where
        def = findDefBy env fun id_unf
        
    go _ _ _ _ = Nothing
    
    extractArgs :: Either InScopeSet SimplEnv -> Bool -> [OutFrame] -> Maybe ([OutTerm], Maybe OutCoercion)
    extractArgs subst trivOnly = goF [] Nothing
      where
        -- Like exprIsConApp_maybe, we expect all arguments to come before any
        -- casts. So only accept an argument when the coercion is Nothing.
        goF args Nothing (App arg : fs)
          | not trivOnly || isTrivialTerm arg
          = goF (subst_arg subst arg : args) Nothing fs
        goF args co_m (Cast co : fs)
          = goF args (Just co'') fs
          where
            co'  = subst_co subst co
            co'' = maybe co' (`mkTransCo` co') co_m
        goF args co_m (Tick ti : fs)
          | not (tickishIsCode ti)
          = goF args co_m fs
        goF args co_m []
          = Just (reverse args, co_m)
        goF _ _ _
          = Nothing
    
    env0 = zapSubstEnvs env
    
    subst_co (Left {})   co = co
    subst_co (Right env) co = substCo env co
    
    subst_arg (Left {})   v = v
    subst_arg (Right env) v = substTerm (text "termIsConApp::subst_arg") env v
    
    subst_frame (Left {})   f = f
    subst_frame (Right env) f = substFrame (text "termIsConApp::subst_frame") env f
    
    extend (Left ins) x v   = Right (extendIdSubst (env0 { se_inScope = ins })
                                                   x (Done v))
    extend (Right env) x v  = Right (extendIdSubst env x (Done v))
    
    -- Largely C&P'd from Simplify.dealWithCoercion
    dealWithCoercion :: Maybe OutCoercion -> DataCon -> [OutTerm]
                     -> Maybe (DataCon, [OutType], [OutTerm])
    dealWithCoercion co_m dc args
      | maybe True isReflCo co_m -- either Nothing or reflexive
      = let (univ_ty_args, rest_args) = splitAtList (dataConUnivTyVars dc) args
        in Just (dc, stripTypeArgs univ_ty_args, rest_args)
      | Just co <- co_m
      , Pair _from_ty to_ty <- coercionKind co
      , Just (to_tc, to_tc_arg_tys) <- splitTyConApp_maybe to_ty
      , to_tc == dataConTyCon dc
            -- These two tests can fail; we might see 
            --      (C x y) `cast` (g :: T a ~ S [a]),
            -- where S is a type function.  In fact, exprIsConApp
            -- will probably not be called in such circumstances,
            -- but there't nothing wrong with it 

      =     -- Here we do the KPush reduction rule as described in the FC paper
            -- The transformation applies iff we have
            --      (C e1 ... en) `cast` co
            -- where co :: (T t1 .. tn) ~ to_ty
            -- The left-hand one must be a T, because exprIsConApp returned True
            -- but the right-hand one might not be.  (Though it usually will.)
            -- (comments from Simplify.dealWithCoercion)
        let
            tc_arity       = tyConArity to_tc
            dc_univ_tyvars = dataConUnivTyVars dc
            dc_ex_tyvars   = dataConExTyVars dc
            arg_tys        = dataConRepArgTys dc

            non_univ_args  = dropList dc_univ_tyvars args
            (ex_args, val_args) = splitAtList dc_ex_tyvars non_univ_args

            -- Make the "theta" from Fig 3 of the paper
            gammas = decomposeCo tc_arity co
            theta_subst = liftCoSubstWith Representational
                             (dc_univ_tyvars ++ dc_ex_tyvars)
                                                    -- existentials are at role N
                             (gammas         ++ map (mkReflCo Nominal)
                                                    (stripTypeArgs ex_args))

              -- Cast the value arguments (which include dictionaries)
            new_val_args = zipWith cast_arg arg_tys val_args
            cast_arg arg_ty arg = mkCast arg (theta_subst arg_ty)

            dump_doc = vcat [ppr dc,      ppr dc_univ_tyvars, ppr dc_ex_tyvars,
                             ppr arg_tys, ppr args,        
                             ppr ex_args, ppr val_args, ppr co, ppr _from_ty, ppr to_ty, ppr to_tc ]
        in
        -- expanding ASSERT2
        if debugIsOn && not (
            eqType _from_ty (mkTyConApp to_tc (stripTypeArgs $ takeList dc_univ_tyvars args)) &&
            all isTypeArg ex_args &&
            equalLength val_args arg_tys)
          then assertPprPanic __FILE__ __LINE__ dump_doc
          else Just (dc, to_tc_arg_tys, ex_args ++ new_val_args)

      | otherwise
      = Nothing

        
    stripTypeArgs args = assert (all isTypeArg args)
                         [ ty | Type ty <- args ]
    
    -- cheating ...
    termFreeVars term = exprFreeVars (termToCoreExpr term)
    
    foldl2 f z xs ys = foldl (\z' (x, y) -> f z' x y) z (zip xs ys)
    
    mkTransCoMaybe Nothing co_m2         = co_m2
    mkTransCoMaybe co_m1 Nothing         = co_m1
    mkTransCoMaybe (Just co1) (Just co2) = Just (mkTransCo co1 co2)

----------------
-- Outputable --
----------------

pprMultiScopedKont :: [ScopedFrame] -> ScopedEnd -> SDoc
pprMultiScopedKont frames end = sep $ punctuate semi (map ppr frames ++ [pprEnd end])
  where
    pprEnd end = ppr end <+> whereClause
    
    whereClause
      | Just mk <- findMetaKont end
      = hang (text "where") 2 (text "ret" <+> equals <+> ppr mk)
      | otherwise
      = empty
    
    findMetaKont (Incoming (StaticEnv env) _) = substKv env
    findMetaKont (Simplified _ mk_m _) = mk_m

instance Outputable SimplEnv where
  ppr env
    =  text "<InScope =" <+> braces (fsep (map ppr (varEnvElts (getInScopeVars (se_inScope env)))))
--    $$ text " Defs      =" <+> ppr defs
    $$ text " IdSubst   =" <+> ppr (se_idSubst env)
    $$ text " TvSubst   =" <+> ppr (se_tvSubst env)
    $$ text " CvSubst   =" <+> ppr (se_cvSubst env)
    $$ text " JvSubst   =" <+> ppr (se_jvSubst env)
    $$ text " RetKont   =" <+> ppr (se_retKont env)
    $$ text " RetTy     =" <+> ppr (se_retTy env)
    $$ text " Context   =" <+> ppr (se_context env)
     <> char '>'

pprTermEnv :: SimplTermEnv -> SDoc
pprTermEnv env
  =  text "<InScope =" <+> braces (fsep (map ppr (varEnvElts (getInScopeVars (se_inScope env)))))
--    $$ text " Defs      =" <+> ppr defs
  $$ text " IdSubst   =" <+> ppr (se_idSubst env)
  $$ text " TvSubst   =" <+> ppr (se_tvSubst env)
  $$ text " CvSubst   =" <+> ppr (se_cvSubst env)
  $$ text " Context   =" <+> ppr (se_context env)
   <> char '>'

instance Outputable StaticEnv where
  ppr (StaticEnv env)
    =  text "<IdSubst   =" <+> ppr (se_idSubst env)
    $$ text " TvSubst   =" <+> ppr (se_tvSubst env)
    $$ text " CvSubst   =" <+> ppr (se_cvSubst env)
    $$ text " JvSubst   =" <+> ppr (se_jvSubst env)
    $$ text " RetKont   =" <+> ppr (se_retKont env)
     <> char '>'

instance Outputable StaticTermEnv where
  ppr (StaticTermEnv env)
    =  text "<IdSubst   =" <+> ppr (se_idSubst env)
    $$ text " TvSubst   =" <+> ppr (se_tvSubst env)
    $$ text " CvSubst   =" <+> ppr (se_cvSubst env)
     <> char '>'

instance Outputable a => Outputable (SubstAns env a) where
  ppr (Done v) = brackets (text "Done:" <+> ppr v)
  ppr (DoneId x) = brackets (text "Id:" <+> ppr x)
  ppr (Susp _env v) = brackets $ hang (text "Suspended:") 2 (pprDeeper (ppr v))

instance Outputable MetaKont where
  ppr (SynKont { mk_frames = frames, mk_end = end })
    = pprMultiScopedKont frames end
  ppr (StrictArg { mk_argInfo = ai
                 , mk_frames = fs
                 , mk_end = end })
    = hang (text "Strict argument to:") 2 $ pprDeeper $
        ppr ai $$ pprMultiScopedKont fs end
  ppr (StrictLet { mk_binder  = bndr
                 , mk_command = command })
    = text "Strict let binding of:" <+> pprBndr LambdaBind bndr $$
      hang (text "In command:") 2 (pprDeeper $ ppr command)
  ppr (StrictLamBind { mk_binder   = bndr
                     , mk_term     = term
                     , mk_coercion = co_m
                     , mk_frames   = fs
                     , mk_end      = end })
    = vcat [ text "Strict lambda-binding of:" <+> pprBndr LambdaBind bndr
           , hang (text "In term:") 2 (pprDeeper $ ppr term)
           , case co_m of Just co -> text "Coercion:" <+> ppr co
                          Nothing -> empty
           , hang (text "With continuation:") 2 (pprMultiScopedKont fs end) ]

instance Outputable Definition where
  ppr (BoundToTerm { def_term = term, def_src = src, def_level = level, def_guidance = guid,
                     def_isConLike = cl, def_isWorkFree = wf, def_isValue = vl,
                     def_isExpandable = ex })
    = sep [brackets (fsep [ppr level, ppr src, ppr guid, ppWhen cl (text "ConLike"),
                           ppWhen wf (text "WorkFree"), ppWhen vl (text "Value"),
                           ppWhen ex (text "Expandable")]),
                           pprDeeper (ppr term)]
  ppr (BoundToJoin { def_join = join, def_src = src, def_guidance = guid })
    = sep [brackets (fsep [ppr NotTopLevel, ppr src, ppr guid, text "Join"]),
                           pprDeeper (ppr join)]
  ppr (BoundToDFun bndrs con args)
    = char '\\' <+> hsep (map ppr bndrs) <+> arrow <+> ppr con <+> hsep (map (parens . ppr) args)
  ppr (NotAmong alts) = text "NotAmong" <+> ppr alts
  ppr NoDefinition = text "NoDefinition"
  
instance Outputable a => Outputable (Scoped env a) where
  ppr (Incoming _ a) = text "<incoming>" <+> ppr a
  ppr (Simplified dup _ a) = ppr dup <+> ppr a

instance Outputable DupFlag where
  ppr OkToDup = text "<ok to dup>"
  ppr NoDup   = text "<no dup>"

instance Outputable Floats where
  ppr (Floats binds ff) = ppr ff $$ ppr (fromOL binds)

instance Outputable FloatFlag where
  ppr FltLifted = text "FltLifted"
  ppr FltOkSpec = text "FltOkSpec"
  ppr FltCareful = text "FltCareful"
