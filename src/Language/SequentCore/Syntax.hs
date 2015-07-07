-- | 
-- Module      : Language.SequentCore.Syntax
-- Description : Sequent Core syntax
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- The AST for Sequent Core, with basic operations.

module Language.SequentCore.Syntax (
  -- * AST Types
  Term(..), Kont(..), Command(..), Bind(..), Alt(..), AltCon(..), Expr(..), Program, KontId,
  SeqCoreTerm, SeqCoreKont, SeqCoreCommand, SeqCoreBind, SeqCoreBndr,
    SeqCoreAlt, SeqCoreExpr, SeqCoreProgram,
  -- * Constructors
  mkCommand, mkLambdas, mkCompute, mkAppTerm, mkConstruction, addLets,
  addLetsToTerm, addNonRec,
  -- * Deconstructors
  lambdas, collectArgs, collectTypeArgs, collectTypeAndOtherArgs, collectArgsUpTo,
  partitionTypes, isLambda,
  isValueArg, isTypeTerm, isCoTerm, isErasedTerm, isRuntimeTerm, isProperTerm,
  isTrivial, isTrivialTerm, isTrivialKont, isReturnKont,
  termIsConstruction, termAsConstruction, splitConstruction,
  commandAsSaturatedCall, asSaturatedCall, asValueCommand,
  flattenBind, flattenBinds, bindersOf, bindersOfBinds,
  -- * Calculations
  termArity, termType, kontType,
  termIsBottom, commandIsBottom,
  needsCaseBinding,
  termOkForSpeculation, commandOkForSpeculation, kontOkForSpeculation,
  termOkForSideEffects, commandOkForSideEffects, kontOkForSideEffects,
  termIsCheap, kontIsCheap, commandIsCheap,
  termIsExpandable, kontIsExpandable, commandIsExpandable,
  -- * Continuation ids
  isKontId, asKontId, Language.SequentCore.WiredIn.mkKontTy, kontTyArg,
  -- * Alpha-equivalence
  (=~=), AlphaEq(..), AlphaEnv, HasId(..)
) where

import {-# SOURCE #-} Language.SequentCore.Pretty ()
import Language.SequentCore.WiredIn

import Coercion  ( Coercion, coercionType, coercionKind )
import CoreSyn   ( AltCon(..), Tickish, tickishCounts, isRuntimeVar
                 , isEvaldUnfolding )
import DataCon   ( DataCon, dataConTyCon, dataConRepArity
                 , dataConUnivTyVars, dataConExTyVars, dataConWorkId )
import Id        ( Id, isDataConWorkId, isDataConWorkId_maybe, isConLikeId
                 , idArity, idType, idDetails, idUnfolding 
                 , setIdType, isBottomingId )
import IdInfo    ( IdDetails(..) )
import Literal   ( Literal, isZeroLit, litIsTrivial, literalType )
import Maybes    ( orElse )
import Outputable
import Pair
import PrimOp    ( PrimOp(..), primOpOkForSpeculation, primOpOkForSideEffects
                 , primOpIsCheap )
import TyCon
import Type      ( Type, KindOrType )
import qualified Type
import TysPrim
import Var       ( Var, isId )
import VarEnv

import Control.Exception ( assert )
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
                | Compute b (Command b)
                                    -- ^ A value produced by a computation.
                                    -- Binds a continuation.
                | Type Type         -- ^ A type. Used to pass a type as an
                                    -- argument to a type-level lambda.
                | Coercion Coercion -- ^ A coercion. Used to pass evidence
                                    -- for the @cast@ operation to a lambda.
                | Kont (Kont b)     -- ^ A continuation. Allowed /only/ as the
                                    -- body of a non-recursive @let@.

-- | A continuation, representing a strict context of a Haskell expression.
-- Computation in the sequent calculus is expressed as the interaction of a
-- value with a continuation.
data Kont b     = App  {- expr -} (Term b) (Kont b)
                  -- ^ Apply the value to an argument.
                | Case {- expr -} b [Alt b]
                  -- ^ Perform case analysis on the value.
                | Cast {- expr -} Coercion (Kont b)
                  -- ^ Cast the value using the given coercion.
                | Tick (Tickish Id) {- expr -} (Kont b)
                  -- ^ Annotate the enclosed frame. Used by the profiler.
                | Return KontId
                  -- ^ Reference to a bound continuation.

-- | The identifier for a covariable, which is like a variable but it binds a
-- continuation.
type KontId = Id

-- | A general computation. A command brings together a list of bindings, some
-- term, and a /continuation/ saying what to do with the value produced by the
-- term. The term and continuation comprise a /cut/ in the sequent calculus.
--
-- __Invariant__: If 'cmdTerm' is a variable representing a constructor, then
-- 'cmdKont' must /not/ begin with as many 'App' frames as the constructor's
-- arity. In other words, the command must not represent a saturated application
-- of a constructor. Such an application should be represented by a 'Cons' value
-- instead. When in doubt, use 'mkCommand' to enforce this invariant.
data Command b  = Command { -- | Bindings surrounding the computation.
                            cmdLet   :: [Bind b]
                            -- | The term producing the value.
                          , cmdTerm :: Term b
                            -- | What to do with the value.
                          , cmdKont  :: Kont b
                          }

-- | A binding. Similar to the @Bind@ datatype from GHC. Can be either a single
-- non-recursive binding or a mutually recursive block.
data Bind b     = NonRec b (Term b) -- ^ A single non-recursive binding.
                | Rec [(b, Term b)] -- ^ A block of mutually recursive bindings.

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
type SeqCoreTerm   = Term   Var
-- | Usual instance of 'Kont', with 'Var's for binders
type SeqCoreKont    = Kont    Var
-- | Usual instance of 'Command', with 'Var's for binders
type SeqCoreCommand = Command Var
-- | Usual instance of 'Bind', with 'Var's for binders
type SeqCoreBind    = Bind    Var
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
mkCommand binds (Compute kbndr (Command { cmdLet = binds'
                                        , cmdTerm = term'
                                        , cmdKont = Return kid })) kont
  | identifier kbndr == kid
  = mkCommand (binds ++ binds') term' kont

mkCommand binds term kont
  = Command { cmdLet = binds, cmdTerm = term, cmdKont = kont }

mkLambdas :: [b] -> Term b -> Term b
mkLambdas = flip (foldr Lam)

mkCompute :: HasId b => b -> Command b -> Term b
-- | Wraps a command that returns to the given continuation id in a term using
-- 'Compute'. If the command is a value command (see 'asValueCommand'), unwraps
-- it instead.
mkCompute k comm
  | Just val <- asValueCommand kid comm
  = val
  | otherwise
  = Compute k comm
  where
    kid = identifier k
  
mkAppTerm :: SeqCoreTerm -> [SeqCoreTerm] -> SeqCoreTerm
mkAppTerm fun args = mkCompute k (mkCommand [] fun (foldr App (Return k) args))
  where
    k = mkArgKontId retTy
    (tyArgs, _) = partitionTypes args
    (_, retTy) = Type.splitFunTys $ Type.applyTys (termType fun) tyArgs

mkConstruction :: DataCon -> [Type] -> [SeqCoreTerm] -> SeqCoreTerm
mkConstruction dc tyArgs valArgs
  = mkAppTerm (Var (dataConWorkId dc)) (map Type tyArgs ++ valArgs)

-- | Adds the given bindings outside those in the given command.
addLets :: [Bind b] -> Command b -> Command b
addLets [] c = c -- avoid unnecessary allocation
addLets bs c = c { cmdLet = bs ++ cmdLet c }

-- | Adds the given binding outside the given command, possibly using a case
-- binding rather than a let. See "CoreSyn" on the let/app invariant.
addNonRec :: HasId b => b -> Term b -> Command b -> Command b
addNonRec bndr rhs comm
  | needsCaseBinding (idType (identifier bndr)) rhs
  = mkCommand [] rhs (Case bndr [Alt DEFAULT [] comm])
  | otherwise
  = addLets [NonRec bndr rhs] comm
  
addLetsToTerm :: [SeqCoreBind] -> SeqCoreTerm -> SeqCoreTerm
addLetsToTerm [] term = term
addLetsToTerm binds term = mkCompute k (mkCommand binds term (Return k))
  where k = mkLetKontId (termType term)

--------------------------------------------------------------------------------
-- Deconstructors
--------------------------------------------------------------------------------

lambdas :: Term b -> ([b], Term b)
lambdas (Lam x body) = (x : xs, body')
  where (xs, body')  = lambdas body
lambdas term         = ([], term)

-- | Divide a continuation into a sequence of arguments and an outer
-- continuation. If @k@ is not an application continuation, then
-- @collectArgs k == ([], k)@.
collectArgs :: Kont b -> ([Term b], Kont b)
collectArgs (App v k)
  = (v : vs, k')
  where (vs, k') = collectArgs k
collectArgs k
  = ([], k)

-- | Divide a continuation into a sequence of type arguments and an outer
-- continuation. If @k@ is not an application continuation or only applies
-- non-type arguments, then @collectTypeArgs k == ([], k)@.
collectTypeArgs :: Kont b -> ([KindOrType], Kont b)
collectTypeArgs (App (Type ty) k)
  = (ty : tys, k')
  where (tys, k') = collectTypeArgs k
collectTypeArgs k
  = ([], k)

-- | Divide a continuation into a sequence of type arguments, then a sequence
-- of non-type arguments, then an outer continuation. If @k@ is not an
-- application continuation, then @collectTypeAndOtherArgs k == ([], [], k)@.
collectTypeAndOtherArgs :: Kont b -> ([KindOrType], [Term b], Kont b)
collectTypeAndOtherArgs k
  = let (tys, k') = collectTypeArgs k
        (vs, k'') = collectArgs k'
    in (tys, vs, k'')

-- | Divide a continuation into a sequence of up to @n@ arguments and an outer
-- continuation. If @k@ is not an application continuation, then
-- @collectArgsUpTo n k == ([], k)@.
collectArgsUpTo :: Int -> Kont b -> ([Term b], Kont b)
collectArgsUpTo 0 k
  = ([], k)
collectArgsUpTo n (App v k)
  = (v : vs, k')
  where (vs, k') = collectArgsUpTo (n - 1) k
collectArgsUpTo _ k
  = ([], k)

-- | Divide a list of terms into an initial sublist of types and the remaining
-- terms.
partitionTypes :: [Term b] -> ([KindOrType], [Term b])
partitionTypes (Type ty : vs) = (ty : tys, vs')
  where (tys, vs') = partitionTypes vs
partitionTypes vs = ([], vs)

-- | True if the given command is a simple lambda, with no let bindings and no
-- continuation.
isLambda :: Command b -> Bool
isLambda (Command { cmdLet = [], cmdKont = Return {}, cmdTerm = Lam {} })
  = True
isLambda _
  = False

isValueArg :: Term b -> Bool
isValueArg (Type _) = False
isValueArg _ = True

-- | True if the given term is a type. See 'Type'.
isTypeTerm :: Term b -> Bool
isTypeTerm (Type _) = True
isTypeTerm _ = False

-- | True if the given term is a coercion. See 'Coercion'.
isCoTerm :: Term b -> Bool
isCoTerm (Coercion _) = True
isCoTerm _ = False

-- | True if the given term is a type or coercion.
isErasedTerm :: Term b -> Bool
isErasedTerm (Type _) = True
isErasedTerm (Coercion _) = True
isErasedTerm _ = False

-- | True if the given term appears at runtime, i.e. is neither a type nor a
-- coercion.
isRuntimeTerm :: Term b -> Bool
isRuntimeTerm v = not (isErasedTerm v)

-- | True if the given term can appear in an expression without restriction.
-- Not true if the term is a type, coercion, or continuation; these can only
-- appear on the RHS of a let or (except for continuations) as an argument in
-- a function call.
isProperTerm :: Term b -> Bool
isProperTerm (Type _)     = False
isProperTerm (Coercion _) = False
isProperTerm (Kont _)     = False
isProperTerm _            = True

-- | True if the given command is so simple we can duplicate it freely. This
-- means it has no bindings and its term and continuation are both trivial.
isTrivial :: HasId b => Command b -> Bool
isTrivial c
  = null (cmdLet c) &&
      isTrivialKont (cmdKont c) &&
      isTrivialTerm (cmdTerm c)

-- | True if the given term is so simple we can duplicate it freely. Some
-- literals are not trivial, and a lambda whose argument is not erased or whose
-- body is non-trivial is also non-trivial.
isTrivialTerm :: HasId b => Term b -> Bool
isTrivialTerm (Lit l)     = litIsTrivial l
isTrivialTerm (Lam x t)   = not (isRuntimeVar (identifier x)) && isTrivialTerm t
isTrivialTerm (Compute _ c) = isTrivial c
isTrivialTerm (Kont kont) = isTrivialKont kont
isTrivialTerm _           = True

-- | True if the given continuation is so simple we can duplicate it freely.
-- This is true of casts and of applications of erased arguments (types and
-- coercions). Ticks are not considered trivial, since this would cause them to
-- be inlined.
isTrivialKont :: Kont b -> Bool
isTrivialKont (Return _) = True
isTrivialKont (Cast _ k) = isTrivialKont k
isTrivialKont (App v k)  = isErasedTerm v && isTrivialKont k
isTrivialKont _          = False

-- | True if the given continuation is a return continuation, @Return _@.
isReturnKont :: Kont b -> Bool
isReturnKont (Return _) = True
isReturnKont _          = False

-- | If a command represents a saturated call to some function, splits it into
-- the function, the arguments, and the remaining continuation after the
-- arguments.
commandAsSaturatedCall :: HasId b =>
                          Command b -> Maybe (Term b, [Term b], Kont b)
commandAsSaturatedCall c
  = do
    let term = cmdTerm c
    (args, kont) <- asSaturatedCall term (cmdKont c)
    return (term, args, kont)

termIsConstruction :: HasId b => Term b -> Bool
termIsConstruction = isJust . termAsConstruction

termAsConstruction :: HasId b => Term b -> Maybe (DataCon, [Type], [Term b])
termAsConstruction (Var id)      | Just dc <- isDataConWorkId_maybe id
                                 , dataConRepArity dc == 0
                                 , null (dataConUnivTyVars dc)
                                 , null (dataConExTyVars dc)
                                 = Just (dc, [], [])
termAsConstruction (Compute k c) = commandAsConstruction (identifier k) c
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

commandAsConstruction :: KontId -> Command b
                      -> Maybe (DataCon, [Type], [Term b])
commandAsConstruction retId (Command { cmdLet = [], cmdTerm = term, cmdKont = kont })
  | Just (dc, tyArgs, valArgs, Return retId') <- splitConstruction term kont
  , retId == retId'
  = Just (dc, tyArgs, valArgs)
commandAsConstruction _ _
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
asValueCommand :: KontId -> Command b -> Maybe (Term b)
asValueCommand k (Command { cmdLet = [], cmdTerm = v, cmdKont = Return k' })
  | k == k'
  = Just v
asValueCommand _ _
  = Nothing

flattenBind :: Bind b -> [(b, Term b)]
flattenBind (NonRec bndr rhs) = [(bndr, rhs)]
flattenBind (Rec pairs)       = pairs

flattenBinds :: [Bind b] -> [(b, Term b)]
flattenBinds = concatMap flattenBind

bindersOf :: Bind b -> [b]
bindersOf (NonRec bndr _) = [bndr]
bindersOf (Rec pairs) = map fst pairs

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
termType (Compute k _)  = kontTyArg (idType (identifier k))
-- see exprType in GHC CoreUtils
termType _other         = alphaTy

-- | Compute the type a continuation accepts. If @kontType kont@ is Foo and @kont@ is bound
-- to @k@, then @k@'s @idType@ will be @!Foo@.
kontType :: HasId b => Kont b -> Type
kontType (Return k)   = kontTyArg (idType k)
kontType (App arg k)  = Type.mkFunTy (termType arg) (kontType k)
kontType (Cast co k)  = let Pair fromTy toTy = coercionKind co
                        in assert (toTy `Type.eqType` kontType k) fromTy
kontType (Case b _)   = idType (identifier b)
kontType (Tick _ k)   = kontType k

-- | Compute (a conservative estimate of) the arity of a term.
termArity :: HasId b => Term b -> Int
termArity (Var x)
  | isId x = idArity x
termArity (Lam _ t)
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
commandIsBottom (Command { cmdTerm = Var x, cmdKont = kont })
  | isBottomingId x
  = go 0 kont
    where
      go n (App arg kont') | isTypeTerm arg = go n kont'
                           | otherwise       = (go $! (n+1)) kont'
      go n (Tick _ kont')  = go n kont'
      go n (Cast _ kont')  = go n kont'
      go n _               = n >= idArity x
commandIsBottom _          = False

-- | Decide whether a term should be bound using @case@ rather than @let@.
-- See 'CoreUtils.needsCaseBinding'.
needsCaseBinding :: Type -> Term b -> Bool
needsCaseBinding ty rhs
  = Type.isUnLiftedType ty && not (termOkForSpeculation rhs)

termOkForSpeculation,    termOkForSideEffects    :: Term b   -> Bool
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
commOk primOpOk (Command { cmdLet = binds, cmdTerm = term, cmdKont = kont })
  = null binds && cutOk primOpOk term kont

cutOk :: (PrimOp -> Bool) -> Term b -> Kont b -> Bool
cutOk primOpOk (Var fid) kont
  | (args, kont') <- collectArgs kont
  = appOk primOpOk fid args && kontOk primOpOk kont'
cutOk primOpOk term kont
  = termOk primOpOk term && kontOk primOpOk kont

kontOk :: (PrimOp -> Bool) -> Kont b -> Bool
kontOk _        (Return _)= False -- TODO Should look at unfolding??
kontOk _        (App _ _) = False
kontOk primOpOk (Case _bndr alts)
  =  all (\(Alt _ _ rhs) -> commOk primOpOk rhs) alts
  && altsAreExhaustive
  where
    altsAreExhaustive
      | (Alt con1 _ _ : _) <- alts
      = case con1 of
          DEFAULT    -> True
          LitAlt {}  -> False
          DataAlt dc -> 1 + length alts == tyConFamilySize (dataConTyCon dc)
      | otherwise
      = False
kontOk primOpOk (Tick ti kont)
  = not (tickishCounts ti) && kontOk primOpOk kont
kontOk primOpOk (Cast _ kont)
  = kontOk primOpOk kont

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

type CheapMeasure = Id -> Int -> Bool

termCheap :: HasId b => CheapMeasure -> Term b -> Bool
termCheap _        (Lit _)      = True
termCheap _        (Var _)      = True
termCheap _        (Type _)     = True
termCheap _        (Coercion _) = True
termCheap appCheap (Lam x t)    = isRuntimeVar (identifier x)
                               || termCheap appCheap t
termCheap appCheap (Compute _ c)= commCheap appCheap c
termCheap appCheap (Kont kont)  = kontCheap appCheap kont

kontCheap :: HasId b => CheapMeasure -> Kont b -> Bool
kontCheap _        (Return _)      = True
kontCheap appCheap (Case _ alts) = all (\(Alt _ _ rhs) -> commCheap appCheap rhs)
                                         alts
kontCheap appCheap (Cast _ kont)   = kontCheap appCheap kont
kontCheap appCheap (Tick ti kont)  = not (tickishCounts ti)
                                   && kontCheap appCheap kont
kontCheap appCheap (App arg kont)  = isErasedTerm arg
                                   && kontCheap appCheap kont

commCheap :: HasId b => CheapMeasure -> Command b -> Bool
commCheap appCheap (Command { cmdLet = binds, cmdTerm = term, cmdKont = kont})
  = all (termCheap appCheap . snd) (flattenBinds binds)
  && cutCheap appCheap term kont

-- See the last clause in CoreUtils.exprIsCheap' for explanations

cutCheap :: HasId b => CheapMeasure -> Term b -> Kont b -> Bool
cutCheap appCheap term (Cast _ kont) = cutCheap appCheap term kont
cutCheap appCheap (Var fid) kont@(App {})
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
    
isCheapApp, isExpandableApp :: CheapMeasure
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

--------------------------------------------------------------------------------
-- Continuation ids
--------------------------------------------------------------------------------

-- | Find whether an id is a continuation id.
isKontId :: Id -> Bool
isKontId x = isKontTy (idType x)

-- | Tag an id as a continuation id.
asKontId :: Id -> KontId
asKontId x | isKontId x = x
           | otherwise  = x `setIdType` mkKontTy (idType x)

kontTyArg :: Type -> Type
kontTyArg ty = isKontTy_maybe ty `orElse` pprPanic "kontTyArg" (ppr ty)

--------------------------------------------------------------------------------
-- Alpha-Equivalence
--------------------------------------------------------------------------------

-- | A class of types that contain an identifier. Useful so that we can compare,
-- say, elements of @Command b@ for any @b@ that wraps an identifier with
-- additional information.
class HasId a where
  -- | The identifier contained by the type @a@.
  identifier :: a -> Id

instance HasId Var where
  identifier x = x

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
  aeqIn env (Compute k1 c1) (Compute k2 c2)
    = aeqIn (rnBndr2 env (identifier k1) (identifier k2)) c1 c2
  aeqIn env (Kont k1) (Kont k2)
    = aeqIn env k1 k2
  aeqIn _ _ _
    = False

instance HasId b => AlphaEq (Kont b) where
  aeqIn env (App c1 k1) (App c2 k2)
    = aeqIn env c1 c2 && aeqIn env k1 k2
  aeqIn env (Case x1 as1) (Case x2 as2)
    = aeqIn env' as1 as2
      where env' = rnBndr2 env (identifier x1) (identifier x2)
  aeqIn env (Cast co1 k1) (Cast co2 k2)
    = aeqIn env co1 co2 && aeqIn env k1 k2
  aeqIn env (Tick ti1 k1) (Tick ti2 k2)
    = ti1 == ti2 && aeqIn env k1 k2
  aeqIn env (Return x1) (Return x2)
    = env `rnOccL` x1 == env `rnOccR` x2
  aeqIn _ _ _
    = False

instance HasId b => AlphaEq (Command b) where
  aeqIn env 
    (Command { cmdLet = bs1, cmdTerm = v1, cmdKont = c1 })
    (Command { cmdLet = bs2, cmdTerm = v2, cmdKont = c2 })
    | Just env' <- aeqBindsIn env bs1 bs2
    = aeqIn env' v1 v2 && aeqIn env' c1 c2
    | otherwise
    = False

-- | If the given lists of bindings are alpha-equivalent, returns an augmented
-- environment tracking the correspondences between the bound variables.
aeqBindsIn :: HasId b => AlphaEnv -> [Bind b] -> [Bind b] -> Maybe AlphaEnv
aeqBindsIn env [] []
  = Just env
aeqBindsIn env (b1:bs1) (b2:bs2)
  = aeqBindIn env b1 b2 >>= \env' -> aeqBindsIn env' bs1 bs2
aeqBindsIn _ _ _
  = Nothing

-- | If the given bindings are alpha-equivalent, returns an augmented environment
-- tracking the correspondences between the bound variables.
aeqBindIn :: HasId b => AlphaEnv -> Bind b -> Bind b -> Maybe AlphaEnv
aeqBindIn env (NonRec x1 c1) (NonRec x2 c2)
  = if aeqIn env' c1 c2 then Just env' else Nothing
  where env' = rnBndr2 env (identifier x1) (identifier x2)
aeqBindIn env (Rec bs1) (Rec bs2)
  = if and $ zipWith alpha bs1 bs2 then Just env' else Nothing
  where
    alpha :: HasId b => (b, Term b) -> (b, Term b) -> Bool
    alpha (_, c1) (_, c2)
      = aeqIn env' c1 c2
    env'
      = rnBndrs2 env (map (identifier . fst) bs1) (map (identifier . fst) bs2)
aeqBindIn _ _ _
  = Nothing

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

instance HasId b => AlphaEq (Bind b) where
  aeqIn env b1 b2 = isJust $ aeqBindIn env b1 b2
