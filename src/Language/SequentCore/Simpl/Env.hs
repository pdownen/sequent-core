{-# LANGUAGE ViewPatterns, BangPatterns, CPP #-}

module Language.SequentCore.Simpl.Env (
  SimplEnv,
  initialEnv, getMode, dynFlags, getSimplRules,
  getUnfoldingInRuleMatch, activeRule,
  
  SimplIdSubst, SubstAns(..),
  substId, substPv, substKv, substTy, substTyVar, substCo, substCoVar,
  substTerm, substKont, substCommand,
  retType,
  extendIdSubst, extendPvSubst, extendTvSubst, extendCvSubst, setRetKont,
  enterScope, enterKontScope, enterScopes, mkFreshVar,
  getTvSubst, getCvSubst,
  zapSubstEnvs,
  
  StaticEnv,
  staticPart, setStaticPart, inDynamicScope,
  zapSubstEnvsStatic,
  
  IdDefEnv, Definition(..), Guidance(..),
  mkBoundTo, mkBoundToPKont, mkDef,
  findDef, setDef, activeUnfolding,
  
  Floats,
  emptyFloats, addNonRecFloat, addRecFloats, zapFloats, zapKontFloats,
  mapFloats, extendFloats, addFloats, wrapFloats, wrapKontFloats, wrapFloatsAroundTerm,
  isEmptyFloats, hasNoKontFloats,
  doFloatFromRhs, getFloatBinds, getFloats,
  
  InCommand, InTerm, InArg, InKont, InFrame, InEnd, InPKont,
  InAlt, InBind, InBndr, InBindPair, InRhs, InValue,
  InType, InCoercion, InId, InPKontId, InVar, InTyVar, InCoVar,
  OutCommand, OutTerm, OutArg, OutKont, OutFrame, OutEnd, OutPKont,
  OutAlt, OutBind, OutBndr, OutBindPair, OutRhs, OutValue,
  OutType, OutCoercion, OutId, OutPKontId, OutVar, OutTyVar, OutCoVar,
  
  termIsHNF, termIsConLike, termIsConApp_maybe
) where

import Language.SequentCore.Arity
import Language.SequentCore.OccurAnal
import Language.SequentCore.Simpl.ExprSize
import Language.SequentCore.Syntax
import Language.SequentCore.Translate
import Language.SequentCore.Util
import Language.SequentCore.WiredIn

import BasicTypes ( Activation, Arity, CompilerPhase(..), PhaseNum
                  , TopLevelFlag(..), RecFlag(..)
                  , isActive, isActiveIn, isEarlyActive
                  , isInlinePragma, inlinePragmaActivation
                  , isTopLevel, isNotTopLevel, isNonRec )
import Coercion   ( Coercion, CvSubstEnv, CvSubst(..)
                  , coercionKind, decomposeCo, isCoVar, isReflCo
                  , liftCoSubstWith, mkCoVarCo, mkReflCo, mkTransCo )
import CoreFVs
import qualified Coercion
import CoreMonad  ( SimplifierMode(..) )
import CoreSyn    ( Tickish(Breakpoint)
                  , Unfolding(..), UnfoldingGuidance(..), UnfoldingSource(..)
                  , isCompulsoryUnfolding, mkOtherCon
                  , tickishCounts, tickishIsCode )
import CoreUnfold ( mkCoreUnfolding, mkDFunUnfolding  )
import DataCon
import DynFlags   ( DynFlags, HasDynFlags, getDynFlags, ufCreationThreshold )
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
                  , eqType, splitTyConApp_maybe, tyVarsOfType
                  , mkTvSubst, mkTyConApp, mkTyVarTy )
import qualified Type
import UniqSupply
import Util       ( debugIsOn
                  , count, dropList, equalLength, takeList, splitAtList )
import Var
import VarEnv
import VarSet

import Control.Applicative ( (<|>) )
import Control.Exception   ( assert )

infixl 1 `setStaticPart`, `inDynamicScope`, `setRetKont`

data SimplGlobalEnv
  = SimplGlobalEnv { sge_dflags   :: DynFlags
                   , sge_mode     :: SimplifierMode
                   , sge_ruleBase :: RuleBase }

data SimplEnv
  = SimplEnv    { se_idSubst :: SimplIdSubst   -- InId      |--> TermSubstAns (in/out)
                , se_pvSubst :: SimplPvSubst   -- InPKontId |--> PKontSubstAns (in/out)
                , se_tvSubst :: TvSubstEnv     -- InTyVar   |--> OutType
                , se_cvSubst :: CvSubstEnv     -- InCoVar   |--> OutCoercion
                , se_retTy   :: Maybe Type
                , se_retKont :: Maybe KontSubstAns
                --  ^^^ static part ^^^  --
                , se_inScope :: InScopeSet     -- OutVar    |--> OutVar
                , se_defs    :: IdDefEnv       -- OutId     |--> Definition (out)
                , se_floats  :: Floats
                , se_global  :: SimplGlobalEnv }

newtype StaticEnv = StaticEnv SimplEnv -- Ignore se_inScope, etc.

type SimplSubst a = IdEnv (SubstAns a) -- InId |--> SubstAns a
data SubstAns a
  = Done (Out a)
  | DoneId OutId
  | Susp StaticEnv (In a)

type SimplIdSubst  = SimplSubst SeqCoreTerm
type SimplPvSubst  = SimplSubst SeqCorePKont
type TermSubstAns  = SubstAns SeqCoreTerm
type PKontSubstAns = SubstAns SeqCorePKont
type KontSubstAns  = SubstAns SeqCoreKont

-- The original simplifier uses the IdDetails stored in a Var to store unfolding
-- info. We store similar data externally instead. (This is based on the Secrets
-- paper, section 6.3.)
type IdDefEnv = IdEnv Definition
data Definition
  = BoundTo { def_term :: OutTerm
            , def_level :: TopLevelFlag
            , def_guidance :: Guidance
            , def_arity :: Arity
            , def_isValue :: Bool
            , def_isConLike :: Bool
            , def_isWorkFree :: Bool
            , def_isExpandable :: Bool
            }
  | BoundToPKont { def_pKont :: OutPKont
                 , def_guidance :: Guidance }
  | BoundToDFun { dfun_bndrs :: [Var]
                , dfun_dataCon :: DataCon
                , dfun_args :: [OutTerm] }
  | NotAmong [AltCon]

data Guidance
  = Never
  | Usually   { guEvenIfUnsat :: Bool
              , guEvenIfBoring :: Bool } -- currently only used when translated
                                         -- from a Core unfolding
  | Sometimes { guSize :: Int
              , guArgDiscounts :: [Int]
              , guResultDiscount :: Int }
              
always :: Guidance
always = Usually { guEvenIfUnsat = True, guEvenIfBoring = True }

mkDef :: (Monad m, HasDynFlags m)
      => SimplEnv -> TopLevelFlag -> OutRhs -> m Definition
mkDef env level rhs
  = do
    dflags <- getDynFlags
    -- FIXME Make a BoundToDFun when possible
    return $ case rhs of
               Left term -> mkBoundTo env dflags term (termArity term) level
               Right pkont -> mkBoundToPKont dflags pkont

mkBoundTo :: SimplEnv -> DynFlags -> OutTerm -> Arity -> TopLevelFlag -> Definition
mkBoundTo env dflags term arity level
  = BoundTo { def_term         = occurAnalyseTerm term
            , def_level        = level
            , def_guidance     = mkGuidance dflags term
            , def_arity        = arity
            , def_isExpandable = termIsExpandable term
            , def_isValue      = termIsHNF env term
            , def_isWorkFree   = termIsCheap term
            , def_isConLike    = termIsConLike env term
            }

mkBoundToPKont :: DynFlags -> OutPKont -> Definition
mkBoundToPKont dflags pkont = BoundToPKont pkont (mkPKontGuidance dflags pkont)

mkGuidance :: DynFlags -> OutTerm -> Guidance
mkGuidance dflags term
  = let cap = ufCreationThreshold dflags
    in case termSize dflags cap term of
       Nothing -> Never
       Just (ExprSize base args res)
         | uncondInline term nValBinds base -> always
         | otherwise                        -> Sometimes base args res
  where
    (bndrs, _) = lambdas term
    nValBinds = length (filter isId bndrs)
    
uncondInline :: OutTerm -> Arity -> Int -> Bool
-- Inline unconditionally if there no size increase
-- Size of call is arity (+1 for the function)
-- See GHC CoreUnfold: Note [INLINE for small functions]
uncondInline rhs arity size 
  | arity > 0 = size <= 10 * (arity + 1)
  | otherwise = isTrivialTerm rhs

mkPKontGuidance :: DynFlags -> OutPKont -> Guidance
mkPKontGuidance dflags pkont
  = let cap = ufCreationThreshold dflags
    in case pKontSize dflags cap pkont of
       Nothing -> Never
       Just (ExprSize base args res) ->
         Sometimes base args res

type In a       = a
type InCommand  = SeqCoreCommand
type InTerm     = SeqCoreTerm
type InArg      = SeqCoreArg
type InKont     = SeqCoreKont
type InFrame    = SeqCoreFrame
type InEnd      = SeqCoreEnd
type InPKont    = SeqCorePKont
type InAlt      = SeqCoreAlt
type InBind     = SeqCoreBind
type InBndr     = SeqCoreBndr
type InBindPair = SeqCoreBindPair
type InRhs      = SeqCoreRhs
type InValue    = SeqCoreValue
type InType     = Type
type InCoercion = Coercion
type InId       = Id
type InPKontId  = PKontId
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
type OutPKont   = SeqCorePKont
type OutAlt     = SeqCoreAlt
type OutBind    = SeqCoreBind
type OutBndr    = SeqCoreBndr
type OutBindPair = SeqCoreBindPair
type OutRhs     = SeqCoreRhs
type OutValue   = SeqCoreValue
type OutType    = Type
type OutCoercion = Coercion
type OutId      = Id
type OutPKontId = PKontId
type OutVar     = Var
type OutTyVar   = TyVar
type OutCoVar   = CoVar

initialEnv :: DynFlags -> SimplifierMode -> RuleBase -> SimplEnv
initialEnv dflags mode rules
  = SimplEnv { se_idSubst = emptyVarEnv
             , se_pvSubst = emptyVarEnv
             , se_tvSubst = emptyVarEnv
             , se_cvSubst = emptyVarEnv
             , se_retTy   = Nothing
             , se_retKont = Nothing
             , se_inScope = emptyInScopeSet
             , se_defs    = emptyVarEnv
             , se_floats  = emptyFloats
             , se_global  = initialGlobalEnv dflags mode rules }
             
initialGlobalEnv :: DynFlags -> SimplifierMode -> RuleBase -> SimplGlobalEnv
initialGlobalEnv dflags mode rules
  = SimplGlobalEnv { sge_dflags   = dflags
                   , sge_mode     = mode
                   , sge_ruleBase = rules }

getMode :: SimplEnv -> SimplifierMode
getMode = sge_mode . se_global

dynFlags :: SimplEnv -> DynFlags
dynFlags = sge_dflags . se_global

getSimplRules :: SimplEnv -> RuleBase
getSimplRules = sge_ruleBase . se_global

activeRule :: SimplEnv -> Activation -> Bool
-- Nothing => No rules at all
activeRule env
  | not (sm_rules mode) = \_ -> False     -- Rewriting is off
  | otherwise           = isActive (sm_phase mode)
  where
    mode = getMode env

enterScope :: SimplEnv -> InVar -> (SimplEnv, OutVar)
enterScope env x
  = (env', x')
  where
    SimplEnv { se_idSubst = ids, se_pvSubst = pvs
             , se_tvSubst = tvs, se_cvSubst = cvs
             , se_inScope = ins, se_defs    = defs } = env
    x1    = uniqAway ins x
    x'    = substIdType env x1
    env'  | isTyVar x   = env { se_tvSubst = tvs', se_inScope = ins', se_defs = defs' }
          | isCoVar x   = env { se_cvSubst = cvs', se_inScope = ins', se_defs = defs' }
          | isPKontId x = env { se_pvSubst = pvs', se_inScope = ins', se_defs = defs' }
          | otherwise   = env { se_idSubst = ids', se_inScope = ins', se_defs = defs' }
    ids'  | x' /= x     = extendVarEnv ids x (DoneId x')
          | otherwise   = delVarEnv ids x
    pvs'  | x' /= x     = extendVarEnv pvs x (DoneId x')
          | otherwise   = delVarEnv pvs x
    tvs'  | x' /= x     = extendVarEnv tvs x (mkTyVarTy x')
          | otherwise   = delVarEnv tvs x
    cvs'  | x' /= x     = extendVarEnv cvs x (mkCoVarCo x')
          | otherwise   = delVarEnv cvs x
    ins'  = extendInScopeSet ins x'
    defs' = delVarEnv defs x'

enterKontScope :: SimplEnv -> Type -> (SimplEnv, Type)
enterKontScope env ty
  = (env { se_pvSubst = emptyVarEnv, se_retTy = Just ty', se_retKont = Nothing }, ty')
  where
    ty' = substTy env ty

enterScopes :: SimplEnv -> [InVar] -> (SimplEnv, [OutVar])
enterScopes env []
  = (env, [])
enterScopes env (x : xs)
  = (env'', x' : xs')
  where
    (env', x') = enterScope env x
    (env'', xs') = enterScopes env' xs

mkFreshVar :: MonadUnique m => SimplEnv -> FastString -> Type -> m (SimplEnv, Var)
mkFreshVar env name ty
  = do
    x <- mkSysLocalM name ty
    let x'   = uniqAway (se_inScope env) x
        env' = env { se_inScope = extendInScopeSet (se_inScope env) x' }
    return (env', x')

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

substPv :: SimplEnv -> InId -> PKontSubstAns
substPv (SimplEnv { se_pvSubst = pvs, se_inScope = ins }) j
  = case lookupVarEnv pvs j of
      Nothing                 -> DoneId (refine ins j)
      Just (DoneId j')        -> DoneId (refine ins j')
      Just ans                -> ans

substKv :: SimplEnv -> KontSubstAns
substKv (SimplEnv { se_retKont = rk, se_retTy = ty })
  = rk `orElse` DoneId kontId
  where
    -- A fake id just so we have something to pass to DoneId
    kontId = mkKontId (ty `orElse` pprPanic "substKv" (text "at top level"))

refine :: InScopeSet -> OutVar -> OutVar
refine ins x
  | isLocalId x
  = case lookupInScope ins x of
      Just x' -> x'
      Nothing -> pprTrace "refine" (text "variable not in scope:" <+> ppr x) x
  | otherwise
  = x

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

substTerm    :: SDoc -> SimplEnv -> SeqCoreTerm    -> SeqCoreTerm
substKont    :: SDoc -> SimplEnv -> SeqCoreKont    -> SeqCoreKont
substCommand :: SDoc -> SimplEnv -> SeqCoreCommand -> SeqCoreCommand

substTerm _doc env term = doSubstT env term
substKont _doc env kont = doSubstK env kont
substCommand _doc env command = doSubstC env command

doSubstT :: SimplEnv -> SeqCoreTerm -> SeqCoreTerm
doSubstT env (Var x)
  = case substId env x of
      DoneId x' -> Var x'
      Done term -> term
      Susp stat term -> doSubstT (stat `inDynamicScope` env) term
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
    (env', ty') = enterKontScope env ty

doSubstK :: SimplEnv -> SeqCoreKont -> SeqCoreKont
doSubstK env (Kont fs end)
  = Kont (map doFrame fs) end'
  where
    doFrame (App arg)
      = App (doSubstT env arg)
    doFrame (Cast co)
      = Cast (substCo env co)
    doFrame (Tick (Breakpoint n ids))
      = Tick (Breakpoint n (map (substIdForId env) ids))
    doFrame (Tick ti)
      = Tick ti
    
    end' = case end of
             Return -> Return
             Case x alts -> Case x' alts'
               where
                 (env', x') = enterScope env x
                 alts' = map doAlt alts
                 doAlt (Alt ac bndrs rhs)
                   = let (env'', bndrs') = enterScopes env' bndrs
                         rhs' = doSubstC env'' rhs
                     in Alt ac bndrs' rhs'

doSubstC :: SimplEnv -> SeqCoreCommand -> SeqCoreCommand
doSubstC env (Let bind body)
  = Let bind' (doSubstC env' body)
  where (env', bind') = doSubstB env bind
doSubstC env (Jump args j)
  = case substPv env j of
      DoneId j' -> Jump args' j'
      Done (PKont bndrs body) -> doSubstC env' body
        where
          env' = foldl extend (zapSubstEnvs env) (bndrs `zip` args')
      Susp stat (PKont bndrs body) -> doSubstC env' body
        where
          env' = foldl extend (stat `inDynamicScope` env) (bndrs `zip` args')
  where
    args' = map (doSubstT env) args
    extend env (bndr, arg) = extendIdSubst env bndr (Done arg)
doSubstC env (Eval v k)
  = Eval (doSubstT env v) (doSubstK env k)
    
doSubstB :: SimplEnv -> SeqCoreBind -> (SimplEnv, SeqCoreBind)
doSubstB env bind
  = case bind of
      NonRec (destBindPair -> (bndr, rhs)) -> (env', NonRec (mkBindPair bndr' rhs'))
        where
          (env', bndr') = enterScope env bndr
          rhs' = doRhs env rhs
      Rec pairs -> (env', Rec (zipWith mkBindPair bndrs' rhss'))
        where
          (bndrs, rhss) = unzip (map destBindPair pairs)
          (env', bndrs') = enterScopes env bndrs
          rhss' = map (doRhs env') rhss
  where
    doRhs env' (Left term)                = Left  (doSubstT env' term)
    doRhs env' (Right (PKont bndrs comm)) = Right (PKont bndrs' (doSubstC env'' comm))
      where (env'', bndrs') = enterScopes env' bndrs

extendIdSubst :: SimplEnv -> InVar -> TermSubstAns -> SimplEnv
extendIdSubst env x rhs
  = env { se_idSubst = extendVarEnv (se_idSubst env) x rhs }

extendPvSubst :: SimplEnv -> InVar -> PKontSubstAns -> SimplEnv
extendPvSubst env x rhs
  = env { se_pvSubst = extendVarEnv (se_pvSubst env) x rhs }

extendTvSubst :: SimplEnv -> InTyVar -> OutType -> SimplEnv
extendTvSubst env@(SimplEnv { se_tvSubst = tvs }) tyVar ty
  = env { se_tvSubst = extendVarEnv tvs tyVar ty }

extendCvSubst :: SimplEnv -> InCoVar -> OutCoercion -> SimplEnv
extendCvSubst env@(SimplEnv { se_cvSubst = cvs }) coVar co
  = env { se_cvSubst = extendVarEnv cvs coVar co }

setRetKont :: SimplEnv -> KontSubstAns -> SimplEnv
setRetKont env ans
  = env { se_retKont = Just ans }

zapSubstEnvs :: SimplEnv -> SimplEnv
zapSubstEnvs env
  = env { se_idSubst = emptyVarEnv
        , se_pvSubst = emptyVarEnv
        , se_tvSubst = emptyVarEnv
        , se_cvSubst = emptyVarEnv
        , se_retKont = Nothing }

setSubstEnvs :: SimplEnv -> [OutBindPair] -> SimplEnv
setSubstEnvs env pairs
  = env { se_idSubst = mkVarEnv [ (id, Done term)  | BindTerm  id term      <- pairs, isId id ]
        , se_pvSubst = mkVarEnv [ (id, Done pkont) | BindPKont id pkont     <- pairs ]
        , se_tvSubst = mkVarEnv [ (tv, ty)         | BindTerm  tv (Type ty) <- pairs ]
        , se_cvSubst = mkVarEnv [ (cv, co)         | BindTerm  cv (Coercion co) <- pairs ]
        , se_retKont = Nothing }

retType :: SimplEnv -> Type
retType env
  | Just ty <- se_retTy env
  = substTy env ty
  | otherwise
  = panic "retType at top level"

staticPart :: SimplEnv -> StaticEnv
staticPart = StaticEnv

setStaticPart :: SimplEnv -> StaticEnv -> SimplEnv
setStaticPart dest (StaticEnv !src)
  = dest { se_idSubst = se_idSubst src
         , se_pvSubst = se_pvSubst src
         , se_tvSubst = se_tvSubst src
         , se_cvSubst = se_cvSubst src
         , se_retTy   = se_retTy   src
         , se_retKont = se_retKont src }

inDynamicScope :: StaticEnv -> SimplEnv -> SimplEnv
inDynamicScope = flip setStaticPart

-- This effectively clears everything but the retTy, since it's the only static
-- part that won't get zapped
zapSubstEnvsStatic :: StaticEnv -> StaticEnv
zapSubstEnvsStatic (StaticEnv env)
  = StaticEnv $ zapSubstEnvs env

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

classifyFF :: SeqCoreBind -> FloatFlag
classifyFF (NonRec (BindTerm bndr rhs))
  | not (isStrictId bndr)    = FltLifted
  | termOkForSpeculation rhs = FltOkSpec
  | otherwise                = FltCareful
classifyFF _ = FltLifted

doFloatFromRhs :: TopLevelFlag -> RecFlag -> Bool -> OutTerm -> SimplEnv -> Bool
-- If you change this function look also at FloatIn.noFloatFromRhs
doFloatFromRhs lvl rc str rhs (SimplEnv {se_floats = Floats fs ff})
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

addNonRecFloat :: SimplEnv -> OutBindPair -> SimplEnv
addNonRecFloat env pair
  = id `seq`   -- This seq forces the Id, and hence its IdInfo,
               -- and hence any inner substitutions
    env { se_floats = se_floats env `addFlts` unitFloat (NonRec pair),
          se_inScope = extendInScopeSet (se_inScope env) id }
  where
    id = binderOfPair pair

mapBinds :: Functor f => (BindPair b -> BindPair b) -> f (Bind b) -> f (Bind b)
mapBinds f pairs = fmap app pairs
  where 
    app (NonRec pair) = NonRec (f pair)
    app (Rec pair)    = Rec (map f pair)

mapFloats :: SimplEnv -> (OutBindPair -> OutBindPair) -> SimplEnv
mapFloats env@SimplEnv { se_floats = Floats fs ff } fun
   = env { se_floats = Floats (mapBinds fun fs) ff }

extendFloats :: SimplEnv -> OutBind -> SimplEnv
-- Add these bindings to the floats, and extend the in-scope env too
extendFloats env bind
  = env { se_floats  = se_floats env `addFlts` unitFloat bind,
          se_inScope = extendInScopeSetList (se_inScope env) bndrs,
          se_defs    = extendVarEnvList (se_defs env) defs}
  where
    bndrs = bindersOf bind
    defs = map asDef (flattenBind bind)
    -- FIXME The NotTopLevel flag might wind up being wrong!
    asDef (BindTerm x term) = (x, mkBoundTo env (dynFlags env) term (termArity term) NotTopLevel)
    asDef (BindPKont p pk)  = (p, mkBoundToPKont (dynFlags env) pk)

addFloats :: SimplEnv -> SimplEnv -> SimplEnv
-- Add the floats for env2 to env1;
-- *plus* the in-scope set for env2, which is bigger
-- than that for env1
addFloats env1 env2
  = env1 {se_floats = se_floats env1 `addFlts` se_floats env2,
          se_inScope = se_inScope env2,
          se_defs = se_defs env2 }

wrapBind :: SeqCoreBind -> SeqCoreCommand -> SeqCoreCommand
wrapBind bind@(Rec {}) cmd = Let bind cmd
wrapBind (NonRec pair) cmd = addNonRec pair cmd

wrapFloats, wrapKontFloats :: SimplEnv -> OutCommand -> OutCommand
wrapFloats env cmd = foldrOL wrapBind cmd (floatBinds (se_floats env))

wrapKontFloats env cmd
  = foldr wrapBind cmd (mapMaybe onlyKonts binds)
  where
    binds = fromOL (floatBinds (se_floats env))
    onlyKonts bind@(NonRec pair) | bindsKont pair = Just bind
                                 | otherwise      = Nothing
    onlyKonts (Rec pairs)        | let pairs' = filter bindsKont pairs
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

wrapFloatsAroundTerm :: SimplEnv -> OutTerm -> OutTerm
wrapFloatsAroundTerm env term
  | isEmptyFloats env
  = term
wrapFloatsAroundTerm env (Compute p comm)
  -- See Note [Wrap around compute]
  = warnPprTrace (not $ hasNoKontFloats env) __FILE__ __LINE__
      (text "cont floats escaping body of command:" <+> ppr comm $$
       text "floats:" <+> brackets (pprWithCommas (ppr . bindersOf)
                                                  (getFloatBinds (getFloats env)))) $
    Compute p (wrapFloats (zapKontFloats env) comm)
wrapFloatsAroundTerm env term
  = mkCompute (termType term) $ wrapFloats env (mkCommand [] term (Kont [] Return))

addFlts :: Floats -> Floats -> Floats
addFlts (Floats bs1 l1) (Floats bs2 l2)
  = Floats (bs1 `appOL` bs2) (l1 `andFF` l2)

zapFloats :: SimplEnv -> SimplEnv
zapFloats  env = env { se_floats  = emptyFloats  }

zapKontFloats :: SimplEnv -> SimplEnv
zapKontFloats env@(SimplEnv { se_floats = Floats fs ff })
  = env { se_floats = Floats fs' ff }
  where
    fs' = toOL . mapMaybe removeKonts . fromOL $ fs
    removeKonts (Rec pairs) | not (null pairs') = Just (Rec pairs')
                            where pairs'        = filter bindsTerm pairs
    removeKonts bind@(NonRec (BindTerm {}))     = Just bind
    removeKonts _                               = Nothing

addRecFloats :: SimplEnv -> SimplEnv -> SimplEnv
-- Flattens the floats from env2 into a single Rec group,
-- prepends the floats from env1, and puts the result back in env2
-- This is all very specific to the way recursive bindings are
-- handled; see Simpl.simplRecBind
addRecFloats env1 env2@(SimplEnv {se_floats = Floats bs ff})
  = assert (case ff of { FltLifted -> True; _ -> False })
  $ env2 {se_floats = se_floats env1 `addFlts` unitFloat (Rec (flattenBinds (fromOL bs)))}

getFloatBinds :: Floats -> [OutBind]
getFloatBinds = fromOL . floatBinds

floatBinds :: Floats -> OrdList OutBind
floatBinds (Floats bs _) = bs

getFloats :: SimplEnv -> Floats
getFloats = se_floats

isEmptyFloats :: SimplEnv -> Bool
isEmptyFloats = isNilOL . floatBinds . se_floats

-- XXX Should we cache this?
hasNoKontFloats :: SimplEnv -> Bool
hasNoKontFloats = foldrOL (&&) True . mapOL (all bindsTerm . flattenBind)
                                    . floatBinds . se_floats

findDefBy :: SimplEnv -> OutId -> (Id -> Unfolding) -> Maybe Definition
findDefBy env var id_unf
  | isStrongLoopBreaker (idOccInfo var)
  = Nothing
  | otherwise
  = lookupVarEnv (se_defs env) var <|> unfoldingToDef (id_unf var)

findDef :: SimplEnv -> OutId -> Maybe Definition
findDef env var
  = findDefBy env var idUnfolding

expandDef_maybe :: Definition -> Maybe SeqCoreTerm
expandDef_maybe (BoundTo { def_isExpandable = True, def_term = term }) = Just term
expandDef_maybe _ = Nothing

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

unfoldingToDef :: Unfolding -> Maybe Definition
unfoldingToDef NoUnfolding     = Nothing
unfoldingToDef (OtherCon cons) = Just (NotAmong cons)
unfoldingToDef unf@(CoreUnfolding {})
  = Just $ BoundTo { def_term         = occurAnalyseTerm (termFromCoreExpr (uf_tmpl unf))
                   , def_level        = if uf_is_top unf then TopLevel else NotTopLevel
                   , def_guidance     = unfGuidanceToGuidance (uf_guidance unf)
                   , def_arity        = uf_arity unf
                   , def_isValue      = uf_is_value unf
                   , def_isConLike    = uf_is_conlike unf
                   , def_isWorkFree   = uf_is_work_free unf
                   , def_isExpandable = uf_expandable unf }
unfoldingToDef unf@(DFunUnfolding {})
  = Just $ BoundToDFun { dfun_bndrs    = df_bndrs unf
                       , dfun_dataCon  = df_con unf
                       , dfun_args     = map (occurAnalyseTerm . termFromCoreExpr)
                                             (df_args unf) }

unfGuidanceToGuidance :: UnfoldingGuidance -> Guidance
unfGuidanceToGuidance UnfNever = Never
unfGuidanceToGuidance (UnfWhen { ug_unsat_ok = unsat , ug_boring_ok = boring })
  = Usually { guEvenIfUnsat = unsat , guEvenIfBoring = boring }
unfGuidanceToGuidance (UnfIfGoodArgs { ug_args = args, ug_size = size, ug_res = res })
  = Sometimes { guSize = size, guArgDiscounts = args, guResultDiscount = res }

setDef :: SimplEnv -> OutId -> Definition -> (SimplEnv, OutId)
setDef env x def
  = (env', x')
  where
    env' = env { se_inScope = extendInScopeSet (se_inScope env) x'
               , se_defs    = extendVarEnv (se_defs env) x' def }
    x'   | DFunUnfolding {} <- idUnfolding x = x -- don't mess with these since
                                                 -- we don't generate them
         | otherwise = x `setIdUnfolding` defToUnfolding def

defToUnfolding :: Definition -> Unfolding
defToUnfolding (NotAmong cons) = mkOtherCon cons
defToUnfolding (BoundToPKont {})
  = NoUnfolding -- TODO Can we do better? Translating requires knowing the outer linear cont.
defToUnfolding (BoundTo { def_term = term, def_level = lev, def_guidance = guid })
  = mkCoreUnfolding InlineRhs (isTopLevel lev) (termToCoreExpr term)
      (termArity term) (guidanceToUnfGuidance guid)
defToUnfolding (BoundToDFun { dfun_bndrs = bndrs, dfun_dataCon = con, dfun_args = args})
  = mkDFunUnfolding bndrs con (map termToCoreExpr args)

guidanceToUnfGuidance :: Guidance -> UnfoldingGuidance
guidanceToUnfGuidance Never = UnfNever
guidanceToUnfGuidance (Usually { guEvenIfUnsat = unsat, guEvenIfBoring = boring })
  = UnfWhen { ug_unsat_ok = unsat, ug_boring_ok = boring }
guidanceToUnfGuidance (Sometimes { guSize = size, guArgDiscounts = args, guResultDiscount = res})
  = UnfIfGoodArgs { ug_size = size, ug_args = args, ug_res = res }

-- TODO This might be in Syntax, but since we're not storing our "unfoldings" in
-- ids, we rely on the environment to tell us whether a variable has been
-- evaluated.

termIsHNF, termIsConLike :: SimplEnv -> SeqCoreTerm -> Bool
termIsHNF     = termIsHNFLike isDataConWorkId defIsEvald
termIsConLike = termIsHNFLike isConLikeId defIsConLike

termIsHNFLike :: (Var -> Bool) -> (Definition -> Bool) -> SimplEnv -> SeqCoreTerm -> Bool
termIsHNFLike isCon isHNFDef env term = isHNFLike term []
  where
    isHNFLike _                fs | hasTick fs = False
    isHNFLike (Var id)         fs = isCon id
                                 || maybe False isHNFDef (findDef env id)
                                 || idArity id > count isRuntimeApp fs
    isHNFLike (Lit {})         _  = True
    isHNFLike (Coercion {})    _  = True
    isHNFLike (Type {})        _  = True
    isHNFLike (Lam x body)     fs = isId x || isHNFLike body fs
    isHNFLike (Compute _ comm) _  = isHNFLikeComm comm
    
    isHNFLikeComm (Let _ comm)  = isHNFLikeComm comm
    isHNFLikeComm (Jump _ j)    = isCon j -- emphasis on constructor-*like*
                                          -- (TODO Let pkont definitions be conlike?)
    isHNFLikeComm (Eval v k)    = case k of
                                    Kont _ (Case {}) -> False
                                    Kont fs Return   -> isHNFLike v fs
    
    isRuntimeApp (App (Type _)) = False
    isRuntimeApp (App _)        = True
    isRuntimeApp _              = False
    
    hasTick fs = or [ tickishCounts ti | Tick ti <- fs ]

defIsEvald :: Definition -> Bool
defIsEvald (NotAmong _) = True
defIsEvald (BoundTo { def_isValue = vl }) = vl
defIsEvald _ = False

defIsConLike :: Definition -> Bool
defIsConLike (NotAmong _) = True
defIsConLike (BoundTo { def_isConLike = cl }) = cl
defIsConLike _ = False

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
    goT :: Either InScopeSet SimplEnv -> SeqCoreTerm
        -> Maybe (DataCon, [Type], [SeqCoreTerm])
    goT subst (Compute _ (Eval v (Kont fs Return))) = go subst v fs Nothing
    goT _     (Compute _ _) = Nothing
    goT subst v             = go subst v [] Nothing
    
    go :: Either InScopeSet SimplEnv -> SeqCoreTerm -> [SeqCoreFrame]
       -> Maybe Coercion
       -> Maybe (DataCon, [Type], [SeqCoreTerm])
    go subst term@(Lam {}) fs co_m
      | Just (args, co_m') <- extractArgs subst fs
      , let (bndrs, body) = lambdas term
      , Compute _ (Eval term' (Kont fs' Return)) <- body
      = let subst' = foldl2 extend subst bndrs args
            co_m'' = mkTransCoMaybe co_m co_m'
        in go subst' term' fs' co_m''
    
    go subst (Compute _ (Eval term (Kont fs' Return))) fs co_m
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
      , Just (args, co_m') <- extractArgs (Left ins) fs
      , count isValueArg args == idArity fun
      = dealWithCoercion (mkTransCoMaybe co_m co_m') dc args
      | Just (BoundToDFun { dfun_bndrs = bndrs
                          , dfun_dataCon = dc
                          , dfun_args = dcArgs }) <- def_m
      , Just (args, co_m') <- extractArgs (Left ins) fs
      , bndrs `equalLength` args
      = let env   = env0 { se_inScope = ins } `setSubstEnvs` zipWith BindTerm bndrs args
            args' = map (substTerm (text "termIsConApp_maybe::go") env) dcArgs
        in dealWithCoercion (mkTransCoMaybe co_m co_m') dc args'
      | Just def <- def_m
      , Just rhs <- expandDef_maybe def
      , def_arity def == 0
      = let ins' = extendInScopeSetSet ins (termFreeVars rhs)
        in go (Left ins') rhs fs co_m
      where
        def_m = findDefBy env fun id_unf
        
    go _ _ _ _ = Nothing
    
    extractArgs :: Either InScopeSet SimplEnv -> [SeqCoreFrame] -> Maybe ([SeqCoreTerm], Maybe Coercion)
    extractArgs = goF [] Nothing
      where
        -- Like exprIsConApp_maybe, we expect all arguments to come before any
        -- casts. So only accept an argument when the coercion is Nothing.
        goF args Nothing subst (App arg : fs)
          = goF (subst_arg subst arg : args) Nothing subst fs
        goF args co_m subst (Cast co : fs)
          = goF args (Just co'') subst fs
          where
            co'  = subst_co subst co
            co'' = maybe co' (`mkTransCo` co') co_m
        goF args co_m subst (Tick ti : fs)
          | not (tickishIsCode ti)
          = goF args co_m subst fs
        goF args co_m _subst []
          = Just (reverse args, co_m)
        goF _ _ _ _
          = Nothing
    
    env0 = zapSubstEnvs env
    
    subst_co (Left {})   co = co
    subst_co (Right env) co = substCo env co
    
    subst_arg (Left {})   v = v
    subst_arg (Right env) v = substTerm (text "termIsConApp::subst_arg") env v
    
    extend (Left ins) x v   = Right (extendIdSubst (env0 { se_inScope = ins })
                                                   x (Done v))
    extend (Right env) x v  = Right (extendIdSubst env x (Done v))
    
    -- Largely C&P'd from Simplify.dealWithCoercion
    dealWithCoercion :: Maybe Coercion -> DataCon -> [SeqCoreTerm]
                     -> Maybe (DataCon, [Type], [SeqCoreTerm])
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

instance Outputable SimplEnv where
  ppr env
    =  text "<InScope =" <+> braces (fsep (map ppr (varEnvElts (getInScopeVars (se_inScope env)))))
--    $$ text " Defs      =" <+> ppr defs
    $$ text " IdSubst   =" <+> ppr (se_idSubst env)
    $$ text " PvSubst   =" <+> ppr (se_pvSubst env)
    $$ text " TvSubst   =" <+> ppr (se_tvSubst env)
    $$ text " CvSubst   =" <+> ppr (se_cvSubst env)
    $$ text " RetTy     =" <+> ppr (se_retTy env)
    $$ text " RetKont   =" <+> ppr (se_retKont env)
    $$ text " Floats    =" <+> ppr floatBndrs
     <> char '>'
    where
      floatBndrs  = bindersOfBinds (getFloatBinds (se_floats env))

instance Outputable StaticEnv where
  ppr (StaticEnv env)
    =  text "<IdSubst   =" <+> ppr (se_idSubst env)
    $$ text " KvSubst   =" <+> ppr (se_pvSubst env)
    $$ text " TvSubst   =" <+> ppr (se_tvSubst env)
    $$ text " CvSubst   =" <+> ppr (se_cvSubst env)
    $$ text " RetTy     =" <+> ppr (se_retTy env)
    $$ text " RetKont   =" <+> ppr (se_retKont env)
     <> char '>'

instance Outputable a => Outputable (SubstAns a) where
  ppr (Done v) = brackets (text "Done:" <+> ppr v)
  ppr (DoneId x) = brackets (text "Id:" <+> ppr x)
  ppr (Susp {}) = text "Suspended"
--  ppr (Susp _env v)
--    = brackets $ hang (text "Suspended:") 2 (ppr v)

instance Outputable Definition where
  ppr (BoundTo { def_term = term, def_level = level, def_guidance = guid,
                 def_isConLike = cl, def_isWorkFree = wf, def_isValue = vl,
                 def_isExpandable = ex })
    = sep [brackets (fsep [ppr level, ppr guid, ppWhen cl (text "ConLike"),
                           ppWhen wf (text "WorkFree"), ppWhen vl (text "Value"),
                           ppWhen ex (text "Expandable")]), ppr term]
  ppr (BoundToPKont pk guid)
    = sep [brackets (ppr guid), ppr pk]
  ppr (BoundToDFun bndrs con args)
    = char '\\' <+> hsep (map ppr bndrs) <+> arrow <+> ppr con <+> hsep (map (parens . ppr) args)
  ppr (NotAmong alts) = text "NotAmong" <+> ppr alts

instance Outputable Guidance where
  ppr Never = text "Never"
  ppr (Usually unsatOk boringOk)
    = text "Usually" <+> brackets (hsep $ punctuate comma $ catMaybes
                                    [if unsatOk then Just (text "even if unsat") else Nothing,
                                     if boringOk then Just (text "even if boring cxt") else Nothing])
  ppr (Sometimes base argDiscs resDisc)
    = text "Sometimes" <+> brackets (int base <+> ppr argDiscs <+> int resDisc)

instance Outputable Floats where
  ppr (Floats binds ff) = ppr ff $$ ppr (fromOL binds)

instance Outputable FloatFlag where
  ppr FltLifted = text "FltLifted"
  ppr FltOkSpec = text "FltOkSpec"
  ppr FltCareful = text "FltCareful"
