-- | 
-- Module      : Language.SequentCore.Syntax
-- Description : Sequent Core syntax
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- The AST for Sequent Core, with basic operations.

module Language.SequentCore.Syntax (
  -- * AST Types
  Term(..), Arg, Kont(..), Frame(..), End(..), PKont(..), Command(..),
  Bind(..), BindPair(..), Rhs,
  Alt(..), AltCon(..), Expr(..), Program, PKontId,
  SeqCoreTerm, SeqCoreArg, SeqCoreKont, SeqCoreFrame, SeqCoreEnd, SeqCorePKont,
    SeqCoreCommand, SeqCoreBind, SeqCoreBindPair, SeqCoreRhs, SeqCoreBndr,
    SeqCoreAlt, SeqCoreExpr, SeqCoreProgram,
  -- * Constructors
  mkCommand, mkVarTerm, mkLambdas, mkCompute, mkComputeEval,
  mkAppTerm, mkCast, mkCastMaybe, castBottomTerm, mkConstruction, mkImpossibleCommand,
  addLets, addLetsToTerm, addNonRec, consFrame, addFrames,
  -- * Deconstructors
  lambdas, collectArgs, collectTypeArgs, collectTypeAndOtherArgs, collectArgsUpTo,
  partitionTypes,
  flattenCommand,
  isValueArg, isTypeArg, isCoArg, isTyCoArg, isAppFrame, isValueAppFrame,
  isTrivial, isTrivialTerm, isTrivialKont, isTrivialPKont, isReturnKont, isReturn,
  isDefaultAlt,
  termIsConstruction, termAsConstruction, splitConstruction,
  commandAsSaturatedCall, asSaturatedCall, asValueCommand,
  binderOfPair, setPairBinder, rhsOfPair, mkBindPair, destBindPair,
  bindsTerm, bindsKont, flattenBind, flattenBinds, bindersOf, bindersOfBinds,
  -- * Calculations
  termType, frameType, termIsBottom, commandIsBottom,
  needsCaseBinding,
  termOkForSpeculation, commandOkForSpeculation, kontOkForSpeculation,
  termOkForSideEffects, commandOkForSideEffects, kontOkForSideEffects,
  termIsCheap, kontIsCheap, commandIsCheap, rhsIsCheap,
  termIsExpandable, kontIsExpandable, commandIsExpandable, rhsIsExpandable,
  CheapAppMeasure, isCheapApp, isExpandableApp,
  termIsCheapBy, kontIsCheapBy, commandIsCheapBy, rhsIsCheapBy,
  applyTypeToArg,
  -- * Continuation ids
  isPKontId, Language.SequentCore.WiredIn.mkKontTy, kontTyArg,
  -- * Values
  Value(..), SeqCoreValue, splitValue, valueToTerm, valueToCommandWith,
  -- * Alpha-equivalence
  (=~=), AlphaEq(..), AlphaEnv, HasId(..)
) where

import {-# SOURCE #-} Language.SequentCore.Pretty ()
import Language.SequentCore.WiredIn

import Coercion  ( Coercion, coercionKind, coercionType, isCoVar, isCoVarType
                 , isReflCo, mkCoCast, mkCoVarCo, mkTransCo )
import CoreSyn   ( AltCon(..), Tickish, tickishCounts, isRuntimeVar
                 , isEvaldUnfolding )
import DataCon   ( DataCon, dataConTyCon, dataConRepArity
                 , dataConUnivTyVars, dataConExTyVars, dataConWorkId )
import Id        ( Id, isDataConWorkId, isDataConWorkId_maybe, isConLikeId
                 , idArity, idType, idDetails, idUnfolding, isBottomingId )
import IdInfo    ( IdDetails(..) )
import Literal   ( Literal, isZeroLit, litIsTrivial, literalType, mkMachString )
import Maybes    ( orElse )
import MkCore    ( rUNTIME_ERROR_ID, mkWildValBinder )
import Outputable
import Pair      ( pSnd )
import PrimOp    ( PrimOp(..), primOpOkForSpeculation, primOpOkForSideEffects
                 , primOpIsCheap )
import TyCon
import Type      ( Type, KindOrType )
import qualified Type
import TysPrim
import Var       ( Var, isId )
import VarEnv

import Data.Maybe

--------------------------------------------------------------------------------
-- AST Types
--------------------------------------------------------------------------------

-- | An expression producing a value. These include literals, lambdas,
-- and variables, as well as types and coercions (see GHC's 'GHC.Expr' for the
-- reasoning). They also include computed values, which bind the current
-- continuation in the body of a command.
data Term b     = Lit Literal       -- ^ A primitive literal value.
                | Var Id            -- ^ A term variable. Must /not/ be a
                                    -- nullary constructor; use 'Cons' for this.
                | Lam b (Term b)    -- ^ A function. Binds some arguments and
                                    -- a continuation. The body is a command.
                | Compute Type (Command b)
                                    -- ^ A value produced by a computation.
                                    -- Binds a continuation.
                | Type Type         -- ^ A type. Used to pass a type as an
                                    -- argument to a type-level lambda.
                | Coercion Coercion -- ^ A coercion. Used to pass evidence
                                    -- for the @cast@ operation to a lambda.

-- | An argument, which can be a regular term or a type or coercion.
type Arg b = Term b

-- | A continuation, representing a strict context of a Haskell expression.
-- Computation in the sequent calculus is expressed as the interaction of a
-- value with a continuation.
data Kont b     = Kont [Frame b] (End b)
                  -- ^ A continuation is expressed as a series of frames
                  -- (usually arguments to apply), followed by a terminal
                  -- action (such as a case analysis).

data Frame b    = App {- expr -} (Arg b)
                  -- ^ Apply the value to an argument.
                | Cast {- expr -} Coercion
                  -- ^ Cast the value using the given coercion.
                | Tick (Tickish Id) {- expr -}
                  -- ^ Annotate the enclosed frame. Used by the profiler.

data End b      = Return
                  -- ^ Pass to the bound continuation.
                | Case {- expr -} b [Alt b]
                  -- ^ Perform case analysis on the value.

-- | A parameterized continuation, otherwise known as a join point. Where a
-- regular continuation represents the context of a single expression, a
-- parameterized continuation is a point in the control flow that many different
-- computations might jump to.
data PKont b    = PKont [b] (Command b)

-- | The identifier for a parameterized continuation, i.e. a join point.
type PKontId = Id

-- | A general computation. A command brings together a list of bindings and
-- either:
--   * A computation to perform, including a /term/ that produces a value and a
--     /continuation/ saying what to do with the value produced by the term; or
--   * A jump to a parameterized continuation, with a list of arguments and the
--     identifier of the continuation.
data Command b = Let (Bind b) (Command b)
               | Eval (Term b) (Kont b)
               | Jump [Arg b] PKontId

-- | The binding of one identifier to one term or continuation.
data BindPair b = BindTerm b (Term b)
                | BindPKont b (PKont b)

-- | A view of the right-hand side of a 'BindPair', whether it binds a term or
-- a parameterized continuation.
type Rhs b = Either (Term b) (PKont b)

-- | A binding. Similar to the @Bind@ datatype from GHC. Can be either a single
-- non-recursive binding or a mutually recursive block.
data Bind b     = NonRec (BindPair b) -- ^ A single non-recursive binding.
                | Rec [BindPair b]    -- ^ A block of mutually recursive bindings.

-- | A case alternative. Given by the head constructor (or literal), a list of
-- bound variables (empty for a literal), and the body as a 'Command'.
data Alt b      = Alt AltCon [b] (Command b)

-- | Some expression -- a term, a command, or a continuation. Useful for
-- writing mutually recursive functions.
data Expr a     = T { unT :: Term a }
                | C { unC :: Command a }
                | K { unK :: Kont a }

-- | An entire program.
type Program a  = [Bind a]

-- | Usual binders for Sequent Core terms
type SeqCoreBndr    = Var
-- | Usual instance of 'Term', with 'Var's for binders
type SeqCoreTerm    = Term    Var
-- | Usual instance of 'Arg', with 'Var's for binders
type SeqCoreArg     = Arg     Var
-- | Usual instance of 'Kont', with 'Var's for binders
type SeqCoreKont    = Kont    Var
-- | Usual instance of 'Kont', with 'Var's for binders
type SeqCoreFrame   = Frame   Var
-- | Usual instance of 'Kont', with 'Var's for binders
type SeqCoreEnd     = End     Var
-- | Usual instance of 'Command', with 'Var's for binders
type SeqCoreCommand = Command Var
-- | Usual instance of 'Bind', with 'Var's for binders
type SeqCoreBind    = Bind    Var
-- | Usual instance of 'BindPair', with 'Var's for binders
type SeqCoreBindPair = BindPair Var
-- | Usual instance of 'Rhs', with 'Var's for binders
type SeqCoreRhs     = Rhs     Var
-- | Usual instance of 'Kont', with 'Var's for binders
type SeqCorePKont   = PKont   Var
-- | Usual instance of 'Alt', with 'Var's for binders
type SeqCoreAlt     = Alt     Var
-- | Usual instance of 'Expr', with 'Var's for binders
type SeqCoreExpr    = Expr    Var
-- | Usual instance of 'Term', with 'Var's for binders
type SeqCoreProgram = Program Var

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

-- | Constructs a command, given @let@ bindings, a term, and a continuation.
--
-- A smart constructor. If the term happens to be a Compute, may fold its
-- command into the result.
mkCommand :: HasId b => [Bind b] -> Term b -> Kont b -> Command b
mkCommand binds (Compute _ comm) kont
  | (binds', Left (term, Kont [] Return)) <- flattenCommand comm
  = mkCommand (binds ++ binds') term kont

mkCommand binds term kont
  = foldr Let (Eval term kont) binds

mkVarTerm :: Var -> SeqCoreTerm
mkVarTerm x | Type.isTyVar x = Type (Type.mkTyVarTy x)
            | Coercion.isCoVar x = Coercion (mkCoVarCo x)
            | otherwise = Var x

mkLambdas :: [b] -> Term b -> Term b
mkLambdas = flip (foldr Lam)

mkCompute :: Type -> Command b -> Term b
-- | Wraps a command that returns to the given continuation id in a term using
-- 'Compute'. If the command is a value command (see 'asValueCommand'), unwraps
-- it instead.
mkCompute ty comm
  | Just val <- asValueCommand comm
  = val
  | otherwise
  = Compute ty comm
  
mkComputeEval :: HasId b => Term b -> [Frame b] -> Term b
mkComputeEval v fs = mkCompute ty (Eval v (Kont fs Return))
  where
    ty = foldl frameType (termType v) fs

mkAppTerm :: SeqCoreTerm -> [SeqCoreTerm] -> SeqCoreTerm
mkAppTerm fun args = mkCompute retTy (Eval fun (Kont (map App args) Return))
  where
    (tyArgs, _) = partitionTypes args
    (_, retTy) = Type.splitFunTys $ Type.applyTys (termType fun) tyArgs

mkCast :: SeqCoreTerm -> Coercion -> SeqCoreTerm
mkCast term co | isReflCo co = term
mkCast (Coercion termCo) co | isCoVarType (pSnd (coercionKind co))
                            = Coercion (mkCoCast termCo co)
-- Unfortunately, our representation isn't good at finding casts at top level.
-- We would need a deep search to find anything besides this very simple case.
-- Fortunately, this should ensure that successive mkCasts accumulate nicely.
mkCast (Compute _ (Eval term (Kont [Cast co1] Return))) co2
  = Compute ty (Eval term (Kont [Cast (mkTransCo co1 co2)] Return))
  where
    ty = pSnd (coercionKind co2)
mkCast term co
  = Compute ty (Eval term (Kont [Cast co] Return))
  where
    ty = pSnd (coercionKind co)

mkCastMaybe :: SeqCoreTerm -> Maybe Coercion -> SeqCoreTerm
mkCastMaybe term Nothing   = term
mkCastMaybe term (Just co) = mkCast term co

castBottomTerm :: SeqCoreTerm -> Type -> SeqCoreTerm
castBottomTerm v ty | termTy `Type.eqType` ty = v
                    | otherwise          = Compute ty (Eval v (Kont [] (Case wild [])))
  where
    termTy = termType v
    wild = mkWildValBinder termTy

mkConstruction :: DataCon -> [Type] -> [SeqCoreTerm] -> SeqCoreTerm
mkConstruction dc tyArgs valArgs
  = mkAppTerm (Var (dataConWorkId dc)) (map Type tyArgs ++ valArgs)

mkImpossibleCommand :: Type -> SeqCoreCommand
mkImpossibleCommand ty
  = Eval (Var rUNTIME_ERROR_ID) (Kont [App (Type ty), App errString] Return)
  where
    errString = Lit (mkMachString "Impossible case alternative")

-- | Adds the given bindings outside those in the given command.
addLets :: [Bind b] -> Command b -> Command b
addLets = flip (foldr Let)

-- | Adds the given binding outside the given command, possibly using a case
-- binding rather than a let. See "CoreSyn" on the let/app invariant.
addNonRec :: HasId b => BindPair b -> Command b -> Command b
addNonRec (BindTerm bndr rhs) comm
  | needsCaseBinding (idType (identifier bndr)) rhs
  = mkCommand [] rhs (Kont [] (Case bndr [Alt DEFAULT [] comm]))
addNonRec pair comm
  = addLets [NonRec pair] comm
  
addLetsToTerm :: [SeqCoreBind] -> SeqCoreTerm -> SeqCoreTerm
addLetsToTerm [] term = term
addLetsToTerm binds term = mkCompute ty (mkCommand binds term (Kont [] Return))
  where
    ty = termType term

consFrame :: Frame b -> Kont b -> Kont b
consFrame f (Kont fs end) = Kont (f : fs) end

addFrames :: [Frame b] -> Kont b -> Kont b
addFrames fs (Kont fs' end) = Kont (fs ++ fs') end

--------------------------------------------------------------------------------
-- Deconstructors
--------------------------------------------------------------------------------

-- | Divide a term into a sequence of lambda-bound variables and a body. If @v@
-- is not a lambda, then @lambdas v == ([], v)@.
lambdas :: Term b -> ([b], Term b)
lambdas (Lam x body) = (x : xs, body')
  where (xs, body')  = lambdas body
lambdas term         = ([], term)

-- | Divide a continuation into a sequence of arguments and an outer
-- continuation. If @k@ is not an application continuation, then
-- @collectArgs k == ([], k)@.
collectArgs :: Kont b -> ([Term b], Kont b)
collectArgs (Kont frames end)
  = go frames
  where
    go (App arg : fs) = (arg : args, k') where (args, k') = go fs
    go fs             = ([], Kont fs end)

-- | Divide a continuation into a sequence of type arguments and an outer
-- continuation. If @k@ is not an application continuation or only applies
-- non-type arguments, then @collectTypeArgs k == ([], k)@.
collectTypeArgs :: Kont b -> ([KindOrType], Kont b)
collectTypeArgs (Kont frames end)
  = go frames
  where
    go (App (Type ty) : fs) = (ty : tys, k') where (tys, k') = go fs
    go fs                   = ([], Kont fs end)

-- | Divide a continuation into a sequence of type arguments, then a sequence
-- of non-type arguments, then an outer continuation. If @k@ is not an
-- application continuation, then @collectTypeAndOtherArgs k == ([], [], k)@.
-- Note that, in general, type and value arguments can be arbitrarily
-- intermingled, so the original continuation cannot necessarily be
-- reconstructed from the returned tuple.
collectTypeAndOtherArgs :: Kont b -> ([KindOrType], [Term b], Kont b)
collectTypeAndOtherArgs k
  = let (tys, k') = collectTypeArgs k
        (vs, k'') = collectArgs k'
    in (tys, vs, k'')

-- | Divide a continuation into a sequence of up to @n@ arguments and an outer
-- continuation. If @k@ is not an application continuation, then
-- @collectArgsUpTo n k == ([], k)@.
collectArgsUpTo :: Int -> Kont b -> ([Term b], Kont b)
collectArgsUpTo n (Kont frames end)
  = go n frames
  where
    go 0 fs
      = ([], Kont fs end)
    go n (App arg : fs)
      = (arg : args, k')
      where (args, k') = go (n - 1) fs
    go _ fs
      = ([], Kont fs end)

-- | Divide a list of terms into an initial sublist of types and the remaining
-- terms.
partitionTypes :: [Term b] -> ([KindOrType], [Term b])
partitionTypes (Type ty : vs) = (ty : tys, vs')
  where (tys, vs') = partitionTypes vs
partitionTypes vs = ([], vs)

flattenCommand :: Command b -> ([Bind b], Either (Term b, Kont b) ([Arg b], PKontId))
flattenCommand = go []
  where
    go binds (Let bind comm) = go (bind:binds) comm
    go binds (Eval term kont)  = (reverse binds, Left (term, kont))
    go binds (Jump args j)   = (reverse binds, Right (args, j))

-- | True if the given term constitutes a value argument rather than a type
-- argument (see 'Type').
isValueArg :: Term b -> Bool
isValueArg (Type _) = False
isValueArg _ = True

-- | True if the given term is a type. See 'Type'.
isTypeArg :: Arg b -> Bool
isTypeArg (Type _) = True
isTypeArg _ = False

-- | True if the given term is a coercion. See 'Coercion'.
isCoArg :: Arg b -> Bool
isCoArg (Coercion _) = True
isCoArg _ = False

-- | True if the given term is a type or a coercion.
isTyCoArg :: Arg b -> Bool
isTyCoArg arg = isTypeArg arg || isCoArg arg

-- | True if the given frame is an argument.
isAppFrame :: Frame b -> Bool
isAppFrame (App {}) = True
isAppFrame _        = False

-- | True if the given frame applies a value argument.
isValueAppFrame :: Frame b -> Bool
isValueAppFrame (App (Type {})) = False
isValueAppFrame (App {})        = True
isValueAppFrame _               = False

-- | True if the given command is so simple we can duplicate it freely. This
-- means it has no bindings and its term and continuation are both trivial.
isTrivial :: HasId b => Command b -> Bool
isTrivial (Let {})       = False
isTrivial (Eval term kont) = isTrivialKont kont && isTrivialTerm term
isTrivial (Jump args _)  = all isTrivialTerm args

-- | True if the given term is so simple we can duplicate it freely. Some
-- literals are not trivial, and a lambda whose argument is not erased or whose
-- body is non-trivial is also non-trivial.
isTrivialTerm :: HasId b => Term b -> Bool
isTrivialTerm (Lit l)     = litIsTrivial l
isTrivialTerm (Lam x t)   = not (isRuntimeVar (identifier x)) && isTrivialTerm t
isTrivialTerm (Compute _ c)  = isTrivial c
isTrivialTerm _           = True

-- | True if the given continuation is so simple we can duplicate it freely.
-- This is true of casts and of applications of erased arguments (types and
-- coercions). Ticks are not considered trivial, since this would cause them to
-- be inlined.
isTrivialKont :: HasId b => Kont b -> Bool
isTrivialKont (Kont fs Return) = all isTrivialFrame fs
isTrivialKont _                = False

isTrivialFrame :: HasId b => Frame b -> Bool
isTrivialFrame (App v)  = isTyCoArg v
isTrivialFrame (Cast _) = True
isTrivialFrame (Tick _) = False

isTrivialPKont :: HasId b => PKont b -> Bool
isTrivialPKont (PKont xs comm) = all (not . isRuntimeVar) (identifiers xs)
                              && isTrivial comm

-- | True if the given continuation is a return continuation, @Kont [] (Return _)@.
isReturnKont :: Kont b -> Bool
isReturnKont (Kont [] Return) = True
isReturnKont _                = False

-- | True if the given continuation end is a return, @Return@.
isReturn :: End b -> Bool
isReturn Return = True
isReturn _      = False

-- | True if the given alternative is a default alternative, @Alt DEFAULT _ _@.
isDefaultAlt :: Alt b -> Bool
isDefaultAlt (Alt DEFAULT _ _) = True
isDefaultAlt _                 = False

-- | If a command represents a saturated call to some function, splits it into
-- the function, the arguments, and the remaining continuation after the
-- arguments.
commandAsSaturatedCall :: HasId b =>
                          Command b -> Maybe (Term b, [Term b], Kont b)
commandAsSaturatedCall (Let _ comm)
  = commandAsSaturatedCall comm
commandAsSaturatedCall (Eval term kont)
  = do
    (args, kont') <- asSaturatedCall term kont
    return (term, args, kont')
commandAsSaturatedCall (Jump {})
  = Nothing

termIsConstruction :: HasId b => Term b -> Bool
termIsConstruction = isJust . termAsConstruction

termAsConstruction :: HasId b => Term b -> Maybe (DataCon, [Type], [Term b])
termAsConstruction (Var id)      | Just dc <- isDataConWorkId_maybe id
                                 , dataConRepArity dc == 0
                                 , null (dataConUnivTyVars dc)
                                 , null (dataConExTyVars dc)
                                 = Just (dc, [], [])
termAsConstruction (Compute _ c) = commandAsConstruction c
termAsConstruction _             = Nothing

splitConstruction :: Term b -> Kont b -> Maybe (DataCon, [Type], [Term b], Kont b)
splitConstruction (Var fid) kont
  | Just dataCon <- isDataConWorkId_maybe fid
  , length valArgs == dataConRepArity dataCon
  = Just (dataCon, tyArgs, valArgs, kont')
  where
    (tyArgs, valArgs, kont') = collectTypeAndOtherArgs kont
splitConstruction _ _
  = Nothing

commandAsConstruction :: Command b
                      -> Maybe (DataCon, [Type], [Term b])
commandAsConstruction (Eval term kont)
  | Just (dc, tyArgs, valArgs, Kont [] Return) <- splitConstruction term kont
  = Just (dc, tyArgs, valArgs)
commandAsConstruction _
  = Nothing

-- | If the given term is a function, and the given continuation would provide
-- enough arguments to saturate it, returns the arguments and the remainder of
-- the continuation.
asSaturatedCall :: HasId b => Term b -> Kont b -> Maybe ([Term b], Kont b)
asSaturatedCall term kont
  | 0 < arity, arity <= length args
  = Just (args, others)
  | otherwise
  = Nothing
  where
    arity = termArity term
    (args, others) = collectArgs kont

-- | If a command does nothing but provide a value to the given continuation id,
-- returns that value.
asValueCommand :: Command b -> Maybe (Term b)
asValueCommand (Eval term (Kont [] Return))
  = Just term
asValueCommand _
  = Nothing

flattenBind :: Bind b -> [BindPair b]
flattenBind (NonRec pair) = [pair]
flattenBind (Rec pairs)   = pairs

flattenBinds :: [Bind b] -> [BindPair b]
flattenBinds = concatMap flattenBind

rhsOfPair :: BindPair b -> Rhs b
rhsOfPair (BindTerm _ v)   = Left v
rhsOfPair (BindPKont _ pk) = Right pk

bindsTerm, bindsKont :: BindPair b -> Bool
bindsTerm (BindTerm {}) = True
bindsTerm (BindPKont {}) = False

bindsKont pair = not (bindsTerm pair)

mkBindPair :: b -> Rhs b -> BindPair b
mkBindPair x = either (BindTerm x) (BindPKont x)

binderOfPair :: BindPair b -> b
binderOfPair (BindTerm x _) = x
binderOfPair (BindPKont j _) = j

setPairBinder :: BindPair b -> b -> BindPair b
setPairBinder (BindTerm _ term) x = BindTerm x term
setPairBinder (BindPKont _ pk)  j = BindPKont j pk

destBindPair :: BindPair b -> (b, Rhs b)
destBindPair pair = (binderOfPair pair, rhsOfPair pair)

bindersOf :: Bind b -> [b]
bindersOf (NonRec pair) = [binderOfPair pair]
bindersOf (Rec pairs) = map binderOfPair pairs

bindersOfBinds :: [Bind b] -> [b]
bindersOfBinds = concatMap bindersOf

--------------------------------------------------------------------------------
-- Calculations
--------------------------------------------------------------------------------

-- | Compute the type of a term.
termType :: HasId b => Term b -> Type
termType (Lit l)        = literalType l
termType (Var x)        = idType x
termType (Lam x t)      = Type.mkPiType (identifier x) (termType t)
termType (Compute ty _) = ty
-- see exprType in GHC CoreUtils
termType _other         = alphaTy

-- | Compute the type of a frame's input, given the type of its input. (The
--   input type of a type application is not uniquely defined, so it must be
--   specified.)
frameType :: HasId b => Type -> Frame b -> Type
frameType ty (App (Type argTy)) = ty `Type.applyTy` argTy
frameType ty (App _)            = Type.funResultTy ty
frameType _  (Cast co)          = pSnd (coercionKind co)
frameType ty (Tick _)           = ty

-- | Compute (a conservative estimate of) the arity of a term.
termArity :: HasId b => Term b -> Int
termArity (Var x)
  | isId x = idArity x
termArity (Lam x t)
  | Type.isTyVar (identifier x)
  = termArity t
  | otherwise
  = 1 + termArity t
termArity _
  = 0

-- | Find whether an expression is definitely bottom.
termIsBottom :: Term b -> Bool
termIsBottom (Var x)       = isBottomingId x && idArity x == 0
termIsBottom (Compute _ c) = commandIsBottom c
termIsBottom _             = False

-- | Find whether a command definitely evaluates to bottom.
commandIsBottom :: Command b -> Bool
commandIsBottom (Let _ comm) = commandIsBottom comm
commandIsBottom (Eval (Var x) (Kont fs _))
  = isBottomingId x && go (0 :: Int) fs
    where
      go n (App (Type _) : fs) = go n fs
      go n (App  _ : fs)   = (go $! (n+1)) fs
      go n (Tick _ : fs)   = go n fs
      go n (Cast _ : fs)   = go n fs
      go n []              = n >= idArity x
commandIsBottom (Jump _ j) = isBottomingId j
commandIsBottom _          = False

-- | Decide whether a term should be bound using @case@ rather than @let@.
-- See 'CoreUtils.needsCaseBinding'.
needsCaseBinding :: Type -> Term b -> Bool
needsCaseBinding ty rhs
  = Type.isUnLiftedType ty && not (termOkForSpeculation rhs)

termOkForSpeculation,    termOkForSideEffects    :: Term b    -> Bool
commandOkForSpeculation, commandOkForSideEffects :: Command b -> Bool
kontOkForSpeculation,    kontOkForSideEffects    :: Kont b    -> Bool

termOkForSpeculation = termOk primOpOkForSpeculation
termOkForSideEffects = termOk primOpOkForSideEffects

commandOkForSpeculation = commOk primOpOkForSpeculation
commandOkForSideEffects = commOk primOpOkForSideEffects

kontOkForSpeculation = kontOk primOpOkForSpeculation
kontOkForSideEffects = kontOk primOpOkForSideEffects

termOk :: (PrimOp -> Bool) -> Term b -> Bool
termOk primOpOk (Var id)         = appOk primOpOk id []
termOk primOpOk (Compute _ comm) = commOk primOpOk comm
termOk _ _                       = True

commOk :: (PrimOp -> Bool) -> Command b -> Bool
commOk primOpOk (Eval term kont) = cutOk primOpOk term kont
commOk _ _                     = False

cutOk :: (PrimOp -> Bool) -> Term b -> Kont b -> Bool
cutOk primOpOk (Var fid) kont
  | (args, kont') <- collectArgs kont
  = appOk primOpOk fid args && kontOk primOpOk kont'
cutOk primOpOk term kont
  = termOk primOpOk term && kontOk primOpOk kont

kontOk :: (PrimOp -> Bool) -> Kont b -> Bool
kontOk primOpOk (Kont frames end) = all frameOk frames && endOk primOpOk end

frameOk :: Frame b -> Bool
frameOk (App (Type _)) = True
frameOk (App _)   = False
frameOk (Tick ti) = not (tickishCounts ti)
frameOk (Cast _)  = True

endOk :: (PrimOp -> Bool) -> End b -> Bool
endOk _ Return = False
endOk primOpOk (Case _bndr alts)
  =  all (\(Alt _ _ rhs) -> commOk primOpOk rhs) alts
  && altsAreExhaustive
  where
    altsAreExhaustive
      | (Alt con1 _ _ : _) <- alts
      = case con1 of
          DEFAULT    -> True
          LitAlt {}  -> False
          DataAlt dc -> length alts == tyConFamilySize (dataConTyCon dc)
      | otherwise
      = False

-- See comments in CoreUtils.app_ok
appOk :: (PrimOp -> Bool) -> Id -> [Term b] -> Bool
appOk primOpOk fid args
  = case idDetails fid of
      DFunId _ newType -> not newType
      DataConWorkId {} -> True
      PrimOpId op      | isDivOp op
                       , [arg1, Lit lit] <- args
                       -> not (isZeroLit lit) && termOk primOpOk arg1
                       | DataToTagOp <- op
                       -> True
                       | otherwise
                       -> primOpOk op && all (termOk primOpOk) args
      _                -> Type.isUnLiftedType (idType fid)
                       || idArity fid > nValArgs
                       || nValArgs == 0 && isEvaldUnfolding (idUnfolding fid)
                       where
                         nValArgs = length (filter isValueArg args)
  where
    isDivOp IntQuotOp        = True
    isDivOp IntRemOp         = True
    isDivOp WordQuotOp       = True
    isDivOp WordRemOp        = True
    isDivOp FloatDivOp       = True
    isDivOp DoubleDivOp      = True
    isDivOp _                = False

termIsCheap, termIsExpandable :: HasId b => Term b -> Bool
termIsCheap      = termCheap isCheapApp
termIsExpandable = termCheap isExpandableApp

kontIsCheap, kontIsExpandable :: HasId b => Kont b -> Bool
kontIsCheap      = kontCheap isCheapApp
kontIsExpandable = kontCheap isExpandableApp

commandIsCheap, commandIsExpandable :: HasId b => Command b -> Bool
commandIsCheap      = commCheap isCheapApp
commandIsExpandable = commCheap isExpandableApp

rhsIsCheap, rhsIsExpandable :: HasId b => Rhs b -> Bool
rhsIsCheap      = rhsCheap isCheapApp
rhsIsExpandable = rhsCheap isExpandableApp

type CheapAppMeasure = Id -> Int -> Bool

termCheap :: HasId b => CheapAppMeasure -> Term b -> Bool
termCheap _        (Lit _)      = True
termCheap _        (Var _)      = True
termCheap _        (Type _)     = True
termCheap _        (Coercion _) = True
termCheap appCheap (Lam x t)    = isRuntimeVar (identifier x)
                               || termCheap appCheap t
termCheap appCheap (Compute _ c)= commCheap appCheap c

kontCheap :: HasId b => CheapAppMeasure -> Kont b -> Bool
kontCheap appCheap (Kont frames end) = all frameCheap frames && endCheap appCheap end

frameCheap :: HasId b => Frame b -> Bool
frameCheap (App arg) = isTyCoArg arg
frameCheap (Cast _)  = True
frameCheap (Tick ti) = not (tickishCounts ti)

endCheap :: HasId b => CheapAppMeasure -> End b -> Bool
endCheap _        Return        = True
endCheap appCheap (Case _ alts) = and [commCheap appCheap rhs | Alt _ _ rhs <- alts]

commCheap :: HasId b => CheapAppMeasure -> Command b -> Bool
commCheap appCheap (Let bind comm)
  = all (bindPairCheap appCheap) (flattenBind bind) && commCheap appCheap comm
commCheap appCheap (Eval term kont)
  = cutCheap appCheap term kont
commCheap appCheap (Jump args j)
  = appCheap j (length (filter isValueArg args))
  
rhsCheap :: HasId b => CheapAppMeasure -> Rhs b -> Bool
rhsCheap appCheap (Left term) = termCheap appCheap term
rhsCheap appCheap (Right (PKont _ comm)) = commCheap appCheap comm

bindPairCheap :: HasId b => CheapAppMeasure -> BindPair b -> Bool
bindPairCheap appCheap = rhsCheap appCheap . rhsOfPair

-- See the last clause in CoreUtils.exprIsCheap' for explanations

cutCheap :: HasId b => CheapAppMeasure -> Term b -> Kont b -> Bool
cutCheap appCheap term (Kont (Cast _ : fs) end)
  = cutCheap appCheap term (Kont fs end)
cutCheap appCheap (Var fid) kont@(Kont (App {} : _) _)
  = case collectTypeAndOtherArgs kont of
      (_, [], kont')   -> kontCheap appCheap kont'
      (_, args, kont')
        | appCheap fid (length args)
        -> papCheap args && kontCheap appCheap kont'
        | otherwise
        -> case idDetails fid of
             RecSelId {}  -> selCheap args
             ClassOpId {} -> selCheap args
             PrimOpId op  -> primOpCheap op args
             _            | isBottomingId fid -> True
                          | otherwise         -> False
  where
    papCheap args       = all (termCheap appCheap) args
    selCheap [arg]      = termCheap appCheap arg
    selCheap _          = False
    primOpCheap op args = primOpIsCheap op && all (termCheap appCheap) args
cutCheap _ _ _ = False
    
isCheapApp, isExpandableApp :: CheapAppMeasure
isCheapApp fid valArgCount = isDataConWorkId fid
                           || valArgCount == 0
                           || valArgCount < idArity fid
isExpandableApp fid valArgCount = isConLikeId fid
                                || valArgCount < idArity fid
                                || allPreds valArgCount (idType fid)
  where
    allPreds 0 _ = True
    allPreds n ty
      | Just (_, ty') <- Type.splitForAllTy_maybe ty = allPreds n ty'
      | Just (argTy, ty') <- Type.splitFunTy_maybe ty
      , Type.isPredTy argTy = allPreds (n-1) ty'
      | otherwise = False

termIsCheapBy    :: HasId b => CheapAppMeasure -> Term b    -> Bool
kontIsCheapBy    :: HasId b => CheapAppMeasure -> Kont b    -> Bool
commandIsCheapBy :: HasId b => CheapAppMeasure -> Command b -> Bool
rhsIsCheapBy     :: HasId b => CheapAppMeasure -> Rhs b     -> Bool

termIsCheapBy    = termCheap
kontIsCheapBy    = kontCheap
commandIsCheapBy = commCheap
rhsIsCheapBy     = rhsCheap

applyTypeToArg :: Type -> Arg b -> Type
applyTypeToArg ty (Type tyArg) = Type.applyTy ty tyArg
applyTypeToArg ty _            = Type.funResultTy ty

--------------------------------------------------------------------------------
-- Continuation ids
--------------------------------------------------------------------------------

-- | Find whether an id is a continuation id.
isPKontId :: Id -> Bool
isPKontId x = isKontTy (idType x)

kontTyArg :: Type -> Type
kontTyArg ty = isKontTy_maybe ty `orElse` pprPanic "kontTyArg" (ppr ty)

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

data Value b
  = LitVal Literal
  | LamVal [b] (Term b)
  | ConsVal DataCon [Type] [Term b]
  
type SeqCoreValue = Value SeqCoreBndr
  
splitValue :: Term b -> Kont b -> Maybe (Value b, Kont b)
splitValue (Lit lit) kont = Just (LitVal lit, kont)
splitValue term@(Lam {}) kont = Just (uncurry LamVal (lambdas term), kont)
splitValue (Var fid) kont
  | Just dc <- isDataConWorkId_maybe fid
  , length valArgs == dataConRepArity dc
  = Just (ConsVal dc tyArgs valArgs, kont')
  where
    (tyArgs, valArgs, kont') = collectTypeAndOtherArgs kont
splitValue _ _               = Nothing

valueToTerm :: SeqCoreValue -> SeqCoreTerm
valueToTerm (LitVal lit)          = Lit lit
valueToTerm (LamVal xs t)         = mkLambdas xs t
valueToTerm (ConsVal dc tys vals) = mkConstruction dc tys vals

valueToCommandWith :: SeqCoreValue -> SeqCoreKont -> SeqCoreCommand
valueToCommandWith (LitVal lit) kont        = mkCommand [] (Lit lit) kont
valueToCommandWith (LamVal xs v) kont       = mkCommand [] (foldr Lam v xs) kont
valueToCommandWith (ConsVal dc tys vs) kont = mkCommand [] (Var (dataConWorkId dc))
                                                           (addFrames (map App (map Type tys ++ vs))
                                                            kont)

--------------------------------------------------------------------------------
-- Alpha-Equivalence
--------------------------------------------------------------------------------

-- | A class of types that contain an identifier. Useful so that we can compare,
-- say, elements of @Command b@ for any @b@ that wraps an identifier with
-- additional information.
class HasId a where
  -- | The identifier contained by the type @a@.
  identifier :: a -> Id
  
  -- | Extract the identifiers from a list of @a@.
  identifiers :: [a] -> [Id]
  identifiers = map identifier

instance HasId Var where
  identifier x = x
  identifiers xs = xs

-- | The type of the environment of an alpha-equivalence comparison. Only needed
-- by user code if two terms need to be compared under some assumed
-- correspondences between free variables. See GHC's 'VarEnv' module for
-- operations.
type AlphaEnv = RnEnv2

infix 4 =~=, `aeq`

-- | The class of types that can be compared up to alpha-equivalence.
class AlphaEq a where
  -- | True if the two given terms are the same, up to renaming of bound
  -- variables.
  aeq :: a -> a -> Bool
  -- | True if the two given terms are the same, up to renaming of bound
  -- variables and the specified equivalences between free variables.
  aeqIn :: AlphaEnv -> a -> a -> Bool

  aeq = aeqIn emptyAlphaEnv

-- | An empty context for alpha-equivalence comparisons.
emptyAlphaEnv :: AlphaEnv
emptyAlphaEnv = mkRnEnv2 emptyInScopeSet

-- | True if the two given terms are the same, up to renaming of bound
-- variables.
(=~=) :: AlphaEq a => a -> a -> Bool
(=~=) = aeq

instance HasId b => AlphaEq (Term b) where
  aeqIn _ (Lit l1) (Lit l2)
    = l1 == l2
  aeqIn env (Lam b1 t1) (Lam b2 t2)
    = aeqIn (rnBndr2 env (identifier b1) (identifier b2)) t1 t2
  aeqIn env (Type t1) (Type t2)
    = aeqIn env t1 t2
  aeqIn env (Coercion co1) (Coercion co2)
    = aeqIn env co1 co2
  aeqIn env (Var x1) (Var x2)
    = env `rnOccL` x1 == env `rnOccR` x2
  aeqIn env (Compute ty1 c1) (Compute ty2 c2)
    = ty1 `Type.eqType` ty2 && aeqIn env c1 c2
  aeqIn _ _ _
    = False

instance HasId b => AlphaEq (Kont b) where
  aeqIn env (Kont fs1 end1) (Kont fs2 end2)
    = aeqIn env fs1 fs2 && aeqIn env end1 end2

instance HasId b => AlphaEq (Frame b) where
  aeqIn env (App v1) (App v2)
    = aeqIn env v1 v2
  aeqIn env (Cast co1) (Cast co2)
    = aeqIn env co1 co2
  aeqIn _   (Tick ti1) (Tick ti2)
    = ti1 == ti2
  aeqIn _ _ _
    = False
    
instance HasId b => AlphaEq (End b) where
  aeqIn _ Return Return
    = True
  aeqIn env (Case x1 as1) (Case x2 as2) 
    = aeqIn env' as1 as2
      where env' = rnBndr2 env (identifier x1) (identifier x2)
  aeqIn _ _ _
    = False

instance HasId b => AlphaEq (PKont b) where
  aeqIn env (PKont xs1 c1) (PKont xs2 c2)
    = aeqIn env' c1 c2
      where env' = rnBndrs2 env (identifiers xs1) (identifiers xs2)

instance HasId b => AlphaEq (Command b) where
  aeqIn env (Let bind1 comm1) (Let bind2 comm2)
    | Just env' <- aeqBindIn env bind1 bind2
    = aeqIn env' comm1 comm2
  aeqIn env (Eval v1 k1) (Eval v2 k2)
    = aeqIn env v1 v2 && aeqIn env k1 k2
  aeqIn env (Jump vs1 j1) (Jump vs2 j2)
    = aeqIn env vs1 vs2 && env `rnOccL` j1 == env `rnOccR` j2
  aeqIn _ _ _
    = False


-- | If the given bindings are alpha-equivalent, returns an augmented environment
-- tracking the correspondences between the bound variables.
aeqBindIn :: HasId b => AlphaEnv -> Bind b -> Bind b -> Maybe AlphaEnv
aeqBindIn env (NonRec pair1) (NonRec pair2)
  = aeqBindPairIn env pair1 pair2
aeqBindIn env (Rec pairs1) (Rec pairs2)
  = if and $ zipWith alpha pairs1 pairs2 then Just env' else Nothing
  where
    alpha pair1 pair2
      = aeqIn env' (rhsOfPair pair1) (rhsOfPair pair2)
    env'
      = rnBndrs2 env (identifiers (map binderOfPair pairs1))
                     (identifiers (map binderOfPair pairs2))
aeqBindIn _ _ _
  = Nothing

aeqBindPairIn :: HasId b => AlphaEnv -> BindPair b -> BindPair b -> Maybe AlphaEnv
aeqBindPairIn env pair1 pair2
  = if aeqIn env' (rhsOfPair pair1) (rhsOfPair pair2) then Just env' else Nothing
  where env' = rnBndr2 env (identifier (binderOfPair pair1))
                           (identifier (binderOfPair pair2))

instance HasId b => AlphaEq (Alt b) where
  aeqIn env (Alt a1 xs1 c1) (Alt a2 xs2 c2)
    = a1 == a2 && aeqIn env' c1 c2
    where
      env' = rnBndrs2 env (map identifier xs1) (map identifier xs2)

instance AlphaEq Type where
  aeqIn env t1 t2
    | Just x1 <- Type.getTyVar_maybe t1
    , Just x2 <- Type.getTyVar_maybe t2
    = env `rnOccL` x1 == env `rnOccR` x2
    | Just (f1, a1) <- Type.splitAppTy_maybe t1
    , Just (f2, a2) <- Type.splitAppTy_maybe t2
    = f1 `alpha` f2 && a1 `alpha` a2
    | Just n1 <- Type.isNumLitTy t1
    , Just n2 <- Type.isNumLitTy t2
    = n1 == n2
    | Just s1 <- Type.isStrLitTy t1
    , Just s2 <- Type.isStrLitTy t2
    = s1 == s2
    | Just (a1, r1) <- Type.splitFunTy_maybe t1
    , Just (a2, r2) <- Type.splitFunTy_maybe t2
    = a1 `alpha` a2 && r1 `alpha` r2
    | Just (c1, as1) <- Type.splitTyConApp_maybe t1
    , Just (c2, as2) <- Type.splitTyConApp_maybe t2
    = c1 == c2 && as1 `alpha` as2
    | Just (x1, t1') <- Type.splitForAllTy_maybe t1
    , Just (x2, t2') <- Type.splitForAllTy_maybe t2
    = aeqIn (rnBndr2 env x1 x2) t1' t2'
    | otherwise
    = False
    where
      alpha a1 a2 = aeqIn env a1 a2

instance AlphaEq Coercion where
  -- Consider coercions equal if their types are equal (proof irrelevance)
  aeqIn env co1 co2 = aeqIn env (coercionType co1) (coercionType co2)
    
instance AlphaEq a => AlphaEq [a] where
  aeqIn env xs ys = and $ zipWith (aeqIn env) xs ys

instance (AlphaEq a, AlphaEq b) => AlphaEq (Either a b) where
  aeqIn env (Left x)  (Left y)  = aeqIn env x y
  aeqIn env (Right x) (Right y) = aeqIn env x y
  aeqIn _   _         _         = False

instance HasId b => AlphaEq (Bind b) where
  aeqIn env b1 b2 = isJust $ aeqBindIn env b1 b2
