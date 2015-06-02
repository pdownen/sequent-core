-- | 
-- Module      : Language.SequentCore.Syntax
-- Description : Sequent Core syntax
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- The AST for Sequent Core, with basic operations.

module Language.SequentCore.Syntax (
  -- * AST Types
  Value(..), Cont(..), Command(..), Bind(..), Alt(..), AltCon(..), ContId,
  SeqCoreValue, SeqCoreCont, SeqCoreCommand, SeqCoreBind, SeqCoreBndr,
    SeqCoreAlt,
  -- * Constructors
  mkCommand, mkCompute, addLets, addNonRec,
  -- * Deconstructors
  lambdas, collectArgs, collectTypeArgs, collectTypeAndOtherArgs, collectArgsUpTo,
  partitionTypes, isLambda,
  isValueArg, isTypeValue, isCoValue, isErasedValue, isRuntimeValue, isProperValue,
  isTrivial, isTrivialValue, isTrivialCont, isReturnCont,
  commandAsSaturatedCall, asSaturatedCall, asValueCommand,
  flattenBind, flattenBinds, bindersOf, bindersOfBinds,
  -- * Calculations
  valueArity, valueType, contType,
  valueIsBottom, commandIsBottom,
  needsCaseBinding,
  valueOkForSpeculation, commandOkForSpeculation, contOkForSpeculation,
  valueOkForSideEffects, commandOkForSideEffects, contOkForSideEffects,
  valueIsCheap, contIsCheap, commandIsCheap,
  valueIsExpandable, contIsExpandable, commandIsExpandable,
  -- * Continuation ids
  contIdTag, isContId, asContId,
  -- * Alpha-equivalence
  (=~=), AlphaEq(..), AlphaEnv, HasId(..)
) where

import {-# SOURCE #-} Language.SequentCore.Pretty ()

import Coercion  ( Coercion, coercionType, coercionKind )
import CoreSyn   ( AltCon(..), Tickish, tickishCounts, isRuntimeVar
                 , isEvaldUnfolding )
import DataCon   ( DataCon, dataConRepType, dataConTyCon )
import Id        ( Id, isDataConWorkId, isDataConWorkId_maybe, isConLikeId
                 , idArity, idType, idDetails, idUnfolding 
                 , idUnique, setIdUnique, isBottomingId )
import IdInfo    ( IdDetails(..) )
import Literal   ( Literal, isZeroLit, litIsTrivial, literalType )
import Outputable
import Pair
import PrimOp    ( PrimOp(..), primOpOkForSpeculation, primOpOkForSideEffects
                 , primOpIsCheap )
import TyCon
import Type      ( Type, KindOrType )
import qualified Type
import TysPrim
import Unique    ( newTagUnique, unpkUnique )
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
data Value b    = Lit Literal       -- ^ A primitive literal value.
                | Var Id            -- ^ A term variable. Must /not/ be a
                                    -- nullary constructor; use 'Cons' for this.
                | Lam [b] b (Command b)
                                    -- ^ A function. Binds some arguments and
                                    -- a continuation. The body is a command.
                | Cons DataCon [Value b]
                                    -- ^ A value formed by a saturated
                                    -- constructor application.
                | Compute b (Command b)
                                    -- ^ A value produced by a computation.
                                    -- Binds a continuation.
                | Type Type         -- ^ A type. Used to pass a type as an
                                    -- argument to a type-level lambda.
                | Coercion Coercion -- ^ A coercion. Used to pass evidence
                                    -- for the @cast@ operation to a lambda.
                | Cont (Cont b)     -- ^ A continuation. Allowed /only/ as the
                                    -- body of a non-recursive @let@.

-- | A continuation, representing a strict context of a Haskell expression.
-- Computation in the sequent calculus is expressed as the interaction of a
-- value with a continuation.
data Cont b     = App  {- expr -} (Value b) (Cont b)
                  -- ^ Apply the value to an argument.
                | Case {- expr -} b Type [Alt b]
                  -- ^ Perform case analysis on the value.
                | Cast {- expr -} Coercion (Cont b)
                  -- ^ Cast the value using the given coercion.
                | Tick (Tickish Id) {- expr -} (Cont b)
                  -- ^ Annotate the enclosed frame. Used by the profiler.
                | Return ContId
                  -- ^ Reference to a bound continuation.

-- | The identifier for a covariable, which is like a variable but it binds a
-- continuation.
type ContId = Id

-- | A general computation. A command brings together a list of bindings, some
-- value, and a /continuation/ saying what to do with that value. The value and
-- continuation comprise a /cut/ in the sequent calculus.
--
-- __Invariant__: If 'cmdValue' is a variable representing a constructor, then
-- 'cmdCont' must /not/ begin with as many 'App' frames as the constructor's
-- arity. In other words, the command must not represent a saturated application
-- of a constructor. Such an application should be represented by a 'Cons' value
-- instead. When in doubt, use 'mkCommand' to enforce this invariant.
data Command b  = Command { -- | Bindings surrounding the computation.
                            cmdLet   :: [Bind b]
                            -- | The value provided to the continuation.
                          , cmdValue :: Value b
                            -- | What to do with the value.
                          , cmdCont  :: Cont b
                          }

-- | A binding. Similar to the @Bind@ datatype from GHC. Can be either a single
-- non-recursive binding or a mutually recursive block.
data Bind b     = NonRec b (Value b) -- ^ A single non-recursive binding.
                | Rec [(b, Value b)] -- ^ A block of mutually recursive bindings.

-- | A case alternative. Given by the head constructor (or literal), a list of
-- bound variables (empty for a literal), and the body as a 'Command'.
data Alt b      = Alt AltCon [b] (Command b)

-- | Usual binders for Sequent Core terms
type SeqCoreBndr    = Var
-- | Usual instance of 'Value', with 'Var's for binders
type SeqCoreValue   = Value   Var
-- | Usual instance of 'Cont', with 'Var's for binders
type SeqCoreCont    = Cont    Var
-- | Usual instance of 'Command', with 'Var's for binders
type SeqCoreCommand = Command Var
-- | Usual instance of 'Bind', with 'Var's for binders
type SeqCoreBind    = Bind    Var
-- | Usual instance of 'Alt', with 'Var's for binders
type SeqCoreAlt     = Alt     Var

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

-- | Constructs a command, given @let@ bindings, a value, and a continuation.
--
-- This smart constructor enforces the invariant that a saturated constructor
-- invocation is represented as a 'Cons' value rather than using 'App' frames.
mkCommand :: HasId b => [Bind b] -> Value b -> Cont b -> Command b
mkCommand binds val@(Var f) cont
  | Just ctor <- isDataConWorkId_maybe f
  , Just (args, cont') <- ctorCall
  = mkCommand binds (Cons ctor args) cont'
  where
    ctorCall
      | 0 <- idArity f
      = Just ([], cont)
      | otherwise
      = asSaturatedCall val cont

mkCommand binds (Compute kbndr (Command { cmdLet = binds'
                                        , cmdValue = val'
                                        , cmdCont = Return kid })) cont
  | identifier kbndr == kid
  = mkCommand (binds ++ binds') val' cont

mkCommand binds val cont
  = Command { cmdLet = binds, cmdValue = val, cmdCont = cont }

mkCompute :: HasId b => b -> Command b -> Value b
-- | Wraps a command that returns to the given continuation id in a value using
-- 'Compute'. If the command is a value command (see 'asValueCommand'), unwraps
-- it instead.
mkCompute k comm
  | Just val <- asValueCommand kid comm
  = val
  | not correctType -- skip the test if it's a value command because idType
                    -- gives a warning if it's a type variable
  = pprPanic "mkCompute" (ppr kid <+> dcolon <+> ppr (idType kid))
  | otherwise
  = Compute k comm
  where
    kid = identifier k
    correctType
      | Just (argTy, retTy) <- Type.splitFunTy_maybe (idType kid)
      = argTy `Type.eqType` retTy
      | otherwise
      = False

-- | Adds the given bindings outside those in the given command.
addLets :: [Bind b] -> Command b -> Command b
addLets [] c = c -- avoid unnecessary allocation
addLets bs c = c { cmdLet = bs ++ cmdLet c }

-- | Adds the given binding outside the given command, possibly using a case
-- binding rather than a let. See "CoreSyn" on the let/app invariant.
addNonRec :: HasId b => b -> Value b -> Command b -> Command b
addNonRec bndr rhs comm
  | needsCaseBinding (idType (identifier bndr)) rhs
  = mkCommand [] rhs (Case bndr (valueType rhs) [Alt DEFAULT [] comm])
  | otherwise
  = addLets [NonRec bndr rhs] comm

--------------------------------------------------------------------------------
-- Deconstructors
--------------------------------------------------------------------------------

lambdas :: Value b -> ([b], Maybe (b, Command b))
lambdas (Lam xs k body) = (xs, Just (k, body))
lambdas _               = ([], Nothing)

-- | Divide a continuation into a sequence of arguments and an outer
-- continuation. If @k@ is not an application continuation, then
-- @collectArgs k == ([], k)@.
collectArgs :: Cont b -> ([Value b], Cont b)
collectArgs (App v k)
  = (v : vs, k')
  where (vs, k') = collectArgs k
collectArgs k
  = ([], k)

-- | Divide a continuation into a sequence of type arguments and an outer
-- continuation. If @k@ is not an application continuation or only applies
-- non-type arguments, then @collectTypeArgs k == ([], k)@.
collectTypeArgs :: Cont b -> ([KindOrType], Cont b)
collectTypeArgs (App (Type ty) k)
  = (ty : tys, k')
  where (tys, k') = collectTypeArgs k
collectTypeArgs k
  = ([], k)

-- | Divide a continuation into a sequence of type arguments, then a sequence
-- of non-type arguments, then an outer continuation. If @k@ is not an
-- application continuation, then @collectTypeAndOtherArgs k == ([], [], k)@.
collectTypeAndOtherArgs :: Cont b -> ([KindOrType], [Value b], Cont b)
collectTypeAndOtherArgs k
  = let (tys, k') = collectTypeArgs k
        (vs, k'') = collectArgs k'
    in (tys, vs, k'')

-- | Divide a continuation into a sequence of up to @n@ arguments and an outer
-- continuation. If @k@ is not an application continuation, then
-- @collectArgsUpTo n k == ([], k)@.
collectArgsUpTo :: Int -> Cont b -> ([Value b], Cont b)
collectArgsUpTo 0 k
  = ([], k)
collectArgsUpTo n (App v k)
  = (v : vs, k')
  where (vs, k') = collectArgsUpTo (n - 1) k
collectArgsUpTo _ k
  = ([], k)

-- | Divide a list of values into an initial sublist of types and the remaining
-- values.
partitionTypes :: [Value b] -> ([KindOrType], [Value b])
partitionTypes (Type ty : vs) = (ty : tys, vs')
  where (tys, vs') = partitionTypes vs
partitionTypes vs = ([], vs)

-- | True if the given command is a simple lambda, with no let bindings and no
-- continuation.
isLambda :: Command b -> Bool
isLambda (Command { cmdLet = [], cmdCont = Return {}, cmdValue = Lam {} })
  = True
isLambda _
  = False

isValueArg :: Value b -> Bool
isValueArg (Type _) = False
isValueArg _ = True

-- | True if the given value is a type. See 'Type'.
isTypeValue :: Value b -> Bool
isTypeValue (Type _) = True
isTypeValue _ = False

-- | True if the given value is a coercion. See 'Coercion'.
isCoValue :: Value b -> Bool
isCoValue (Coercion _) = True
isCoValue _ = False

-- | True if the given value is a type or coercion.
isErasedValue :: Value b -> Bool
isErasedValue (Type _) = True
isErasedValue (Coercion _) = True
isErasedValue _ = False

-- | True if the given value appears at runtime, i.e. is neither a type nor a
-- coercion.
isRuntimeValue :: Value b -> Bool
isRuntimeValue v = not (isErasedValue v)

-- | True if the given value can appear in an expression without restriction.
-- Not true if the value is a type, coercion, or continuation; these can only
-- appear on the RHS of a let or (except for continuations) as an argument in
-- a function call.
isProperValue :: Value b -> Bool
isProperValue (Type _)     = False
isProperValue (Coercion _) = False
isProperValue (Cont _)     = False
isProperValue _            = True

-- | True if the given command is so simple we can duplicate it freely. This
-- means it has no bindings and its value and continuation are both trivial.
isTrivial :: HasId b => Command b -> Bool
isTrivial c
  = null (cmdLet c) &&
      isTrivialCont (cmdCont c) &&
      isTrivialValue (cmdValue c)

-- | True if the given value is so simple we can duplicate it freely. Some
-- literals are not trivial, and a lambda whose argument is not erased or whose
-- body is non-trivial is also non-trivial.
isTrivialValue :: HasId b => Value b -> Bool
isTrivialValue (Lit l)     = litIsTrivial l
isTrivialValue (Lam xs _ c)= not (any (isRuntimeVar . identifier) xs) && isTrivial c
isTrivialValue (Cons _ as) = all isErasedValue as
isTrivialValue (Compute _ c) = isTrivial c
isTrivialValue (Cont cont) = isTrivialCont cont
isTrivialValue _           = True

-- | True if the given continuation is so simple we can duplicate it freely.
-- This is true of casts and of applications of erased arguments (types and
-- coercions). Ticks are not considered trivial, since this would cause them to
-- be inlined.
isTrivialCont :: Cont b -> Bool
isTrivialCont (Return _) = True
isTrivialCont (Cast _ k) = isTrivialCont k
isTrivialCont (App v k)  = isErasedValue v && isTrivialCont k
isTrivialCont _          = False

-- | True if the given continuation is a return continuation, @Return _@.
isReturnCont :: Cont b -> Bool
isReturnCont (Return _) = True
isReturnCont _          = False

-- | If a command represents a saturated call to some function, splits it into
-- the function, the arguments, and the remaining continuation after the
-- arguments.
commandAsSaturatedCall :: HasId b =>
                          Command b -> Maybe (Value b, [Value b], Cont b)
commandAsSaturatedCall c
  = do
    let val = cmdValue c
    (args, cont) <- asSaturatedCall val (cmdCont c)
    return $ (val, args, cont)

-- | If the given value is a function, and the given continuation would provide
-- enough arguments to saturate it, returns the arguments and the remainder of
-- the continuation.
asSaturatedCall :: HasId b => Value b -> Cont b -> Maybe ([Value b], Cont b)
asSaturatedCall val cont
  | 0 < arity, arity <= length args
  = Just (args, others)
  | otherwise
  = Nothing
  where
    arity = valueArity val
    (args, others) = collectArgs cont

-- | If a command does nothing but provide a value to the given continuation id,
-- returns that value.
asValueCommand :: ContId -> Command b -> Maybe (Value b)
asValueCommand k (Command { cmdLet = [], cmdValue = v, cmdCont = Return k' })
  | k == k'
  = Just v
asValueCommand _ _
  = Nothing

flattenBind :: Bind b -> [(b, Value b)]
flattenBind (NonRec bndr rhs) = [(bndr, rhs)]
flattenBind (Rec pairs)       = pairs

flattenBinds :: [Bind b] -> [(b, Value b)]
flattenBinds = concatMap flattenBind

bindersOf :: Bind b -> [b]
bindersOf (NonRec bndr _) = [bndr]
bindersOf (Rec pairs) = map fst pairs

bindersOfBinds :: [Bind b] -> [b]
bindersOfBinds = concatMap bindersOf

--------------------------------------------------------------------------------
-- Calculations
--------------------------------------------------------------------------------

-- | Compute the type of a value.
valueType :: HasId b => Value b -> Type
valueType (Lit l)        = literalType l
valueType (Var x)        = idType x
valueType (Lam xs k _)   = Type.mkPiTypes (map identifier xs) retTy
  where
    retTy = Type.funArgTy (idType (identifier k))
valueType (Cons con as)  = res_ty
  where
    (tys, _) = partitionTypes as
    (_, res_ty) = Type.splitFunTys (dataConRepType con `Type.applyTys` tys)
valueType (Compute k _)  = Type.funArgTy (idType (identifier k))
-- see exprType in GHC CoreUtils
valueType _other         = alphaTy

-- | Compute the type a continuation accepts. IMPORTANT: This is *not* the type
-- that a cont identifier will be assigned; for compatibility with Core, a
-- ContId's type is a function type from the accepted type to the type of the
-- continuation's static context.
contType :: HasId b => Cont b -> Type
contType (Return k)   = Type.funArgTy (idType k)
contType (App arg k)  = Type.mkFunTy (valueType arg) (contType k)
contType (Cast co k)  = let Pair fromTy toTy = coercionKind co
                        in assert (toTy `Type.eqType` contType k) fromTy
contType (Case b _ _) = idType (identifier b)
contType (Tick _ k)   = contType k

-- | Compute (a conservative estimate of) the arity of a value.
valueArity :: HasId b => Value b -> Int
valueArity (Var x)
  | isId x = idArity x
valueArity (Lam bndrs _kbndr _)
  = length bndrs
valueArity _
  = 0

-- | Find whether an expression is definitely bottom.
valueIsBottom :: Value b -> Bool
valueIsBottom (Var x)       = isBottomingId x && idArity x == 0
valueIsBottom (Compute _ c) = commandIsBottom c
valueIsBottom _             = False

-- | Find whether a command definitely evaluates to bottom.
commandIsBottom :: Command b -> Bool
commandIsBottom (Command { cmdValue = Var x, cmdCont = cont })
  | isBottomingId x
  = go 0 cont
    where
      go n (App arg cont') | isTypeValue arg = go n cont'
                           | otherwise       = (go $! (n+1)) cont'
      go n (Tick _ cont')  = go n cont'
      go n (Cast _ cont')  = go n cont'
      go n _               = n >= idArity x
commandIsBottom _          = False

-- | Decide whether a value should be bound using @case@ rather than @let@.
-- See 'CoreUtils.needsCaseBinding'.
needsCaseBinding :: Type -> Value b -> Bool
needsCaseBinding ty rhs
  = Type.isUnLiftedType ty && not (valueOkForSpeculation rhs)

valueOkForSpeculation,   valueOkForSideEffects   :: Value b   -> Bool
commandOkForSpeculation, commandOkForSideEffects :: Command b -> Bool
contOkForSpeculation,    contOkForSideEffects    :: Cont b    -> Bool

valueOkForSpeculation = valOk primOpOkForSpeculation
valueOkForSideEffects = valOk primOpOkForSideEffects

commandOkForSpeculation = commOk primOpOkForSpeculation
commandOkForSideEffects = commOk primOpOkForSideEffects

contOkForSpeculation = contOk primOpOkForSpeculation
contOkForSideEffects = contOk primOpOkForSideEffects

valOk :: (PrimOp -> Bool) -> Value b -> Bool
valOk primOpOk (Var id)         = appOk primOpOk id []
valOk primOpOk (Compute _ comm) = commOk primOpOk comm
valOk _ _                       = True

commOk :: (PrimOp -> Bool) -> Command b -> Bool
commOk primOpOk (Command { cmdLet = binds, cmdValue = val, cmdCont = cont })
  = null binds && cutOk primOpOk val cont

cutOk :: (PrimOp -> Bool) -> Value b -> Cont b -> Bool
cutOk primOpOk (Var fid) cont
  | (args, cont') <- collectArgs cont
  = appOk primOpOk fid args && contOk primOpOk cont'
cutOk primOpOk val cont
  = valOk primOpOk val && contOk primOpOk cont

contOk :: (PrimOp -> Bool) -> Cont b -> Bool
contOk _        (Return _)= False -- TODO Should look at unfolding??
contOk _        (App _ _) = False
contOk primOpOk (Case _bndr _ty alts)
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
contOk primOpOk (Tick ti cont)
  = not (tickishCounts ti) && contOk primOpOk cont
contOk primOpOk (Cast _ cont)
  = contOk primOpOk cont

-- See comments in CoreUtils.app_ok
appOk :: (PrimOp -> Bool) -> Id -> [Value b] -> Bool
appOk primOpOk fid args
  = case idDetails fid of
      DFunId _ newType -> not newType
      DataConWorkId {} -> True
      PrimOpId op      | isDivOp op
                       , [arg1, Lit lit] <- args
                       -> not (isZeroLit lit) && valOk primOpOk arg1
                       | DataToTagOp <- op
                       -> True
                       | otherwise
                       -> primOpOk op && all (valOk primOpOk) args
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

valueIsCheap, valueIsExpandable :: HasId b => Value b -> Bool
valueIsCheap      = valCheap isCheapApp
valueIsExpandable = valCheap isExpandableApp

contIsCheap, contIsExpandable :: HasId b => Cont b -> Bool
contIsCheap      = contCheap isCheapApp
contIsExpandable = contCheap isExpandableApp

commandIsCheap, commandIsExpandable :: HasId b => Command b -> Bool
commandIsCheap      = commCheap isCheapApp
commandIsExpandable = commCheap isExpandableApp

type CheapMeasure = Id -> Int -> Bool

valCheap :: HasId b => CheapMeasure -> Value b -> Bool
valCheap _        (Lit _)      = True
valCheap _        (Var _)      = True
valCheap _        (Type _)     = True
valCheap _        (Coercion _) = True
valCheap _        (Cons _ _)   = True
valCheap appCheap (Lam xs _ c) = any (isRuntimeVar . identifier) xs
                               || commCheap appCheap c
valCheap appCheap (Compute _ c)= commCheap appCheap c
valCheap appCheap (Cont cont)  = contCheap appCheap cont

contCheap :: HasId b => CheapMeasure -> Cont b -> Bool
contCheap _        (Return _)      = True
contCheap appCheap (Case _ _ alts) = all (\(Alt _ _ rhs) -> commCheap appCheap rhs)
                                         alts
contCheap appCheap (Cast _ cont)   = contCheap appCheap cont
contCheap appCheap (Tick ti cont)  = not (tickishCounts ti)
                                   && contCheap appCheap cont
contCheap appCheap (App arg cont)  = isErasedValue arg
                                   && contCheap appCheap cont

commCheap :: HasId b => CheapMeasure -> Command b -> Bool
commCheap appCheap (Command { cmdLet = binds, cmdValue = val, cmdCont = cont})
  = all (valCheap appCheap . snd) (flattenBinds binds)
  && cutCheap appCheap val cont

-- See the last clause in CoreUtils.exprIsCheap' for explanations

cutCheap :: HasId b => CheapMeasure -> Value b -> Cont b -> Bool
cutCheap appCheap val (Cast _ cont) = cutCheap appCheap val cont
cutCheap appCheap (Var fid) cont@(App {})
  = case collectTypeAndOtherArgs cont of
      (_, [], cont')   -> contCheap appCheap cont'
      (_, args, cont')
        | appCheap fid (length args)
        -> papCheap args && contCheap appCheap cont'
        | otherwise
        -> case idDetails fid of
             RecSelId {}  -> selCheap args
             ClassOpId {} -> selCheap args
             PrimOpId op  -> primOpCheap op args
             _            | isBottomingId fid -> True
                          | otherwise         -> False
  where
    papCheap args       = all (valCheap appCheap) args
    selCheap [arg]      = valCheap appCheap arg
    selCheap _          = False
    primOpCheap op args = primOpIsCheap op && all (valCheap appCheap) args
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

-- | INTERNAL USE ONLY.
contIdTag :: Char
-- TODO Yuck. Find a way around this by any means necessary.
-- Should be different from any unique tag used anywhere else (!!)
contIdTag = 'Q'

-- | Find whether an id is a continuation id.
isContId :: Id -> Bool
isContId x = tag == contIdTag where (tag, _) = unpkUnique (idUnique x) -- barf

-- | Tag an id as a continuation id. This changes the unique of the id, so the
-- returned id is always distinct from the argument in comparisons.
asContId :: Id -> ContId
asContId x = x `setIdUnique` uniq'
  where
    uniq' = newTagUnique (idUnique x) contIdTag

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

instance HasId b => AlphaEq (Value b) where
  aeqIn _ (Lit l1) (Lit l2)
    = l1 == l2
  aeqIn env (Lam bs1 k1 c1) (Lam bs2 k2 c2)
    = aeqIn (rnBndrs2 env' (map identifier bs1) (map identifier bs2)) c1 c2
    where env' = rnBndr2 env (identifier k1) (identifier k2)
  aeqIn env (Type t1) (Type t2)
    = aeqIn env t1 t2
  aeqIn env (Coercion co1) (Coercion co2)
    = aeqIn env co1 co2
  aeqIn env (Var x1) (Var x2)
    = env `rnOccL` x1 == env `rnOccR` x2
  aeqIn env (Compute k1 c1) (Compute k2 c2)
    = aeqIn (rnBndr2 env (identifier k1) (identifier k2)) c1 c2
  aeqIn env (Cont k1) (Cont k2)
    = aeqIn env k1 k2
  aeqIn _ _ _
    = False

instance HasId b => AlphaEq (Cont b) where
  aeqIn env (App c1 k1) (App c2 k2)
    = aeqIn env c1 c2 && aeqIn env k1 k2
  aeqIn env (Case x1 t1 as1) (Case x2 t2 as2)
    = aeqIn env' t1 t2 && aeqIn env' as1 as2
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
    (Command { cmdLet = bs1, cmdValue = v1, cmdCont = c1 })
    (Command { cmdLet = bs2, cmdValue = v2, cmdCont = c2 })
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
    alpha :: HasId b => (b, Value b) -> (b, Value b) -> Bool
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
