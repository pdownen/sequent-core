-- | 
-- Module      : Language.SequentCore.Syntax
-- Description : Sequent Core syntax
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental
--
-- The AST for Sequent Core, with basic operations.

module Language.SequentCore.Syntax (
  -- * AST Types
  Value(..), Frame(..), Cont, Command(..), Bind(..), Alt(..), AltCon(..),
  SeqCoreValue, SeqCoreFrame, SeqCoreCont, SeqCoreCommand, SeqCoreBind,
    SeqCoreAlt,
  -- * Constructors
  mkCommand, valueCommand, varCommand, lambdas, addLets, extendCont,
  -- * Deconstructors
  collectLambdas, collectArgs, isLambda,
  isTypeArg, isCoArg, isErasedArg, isRuntimeArg,
  isTypeValue, isCoValue, isErasedValue, isRuntimeValue,
  isTrivial, isTrivialValue, isTrivialCont, isTrivialFrame,
  commandAsSaturatedCall, asSaturatedCall, asValueCommand,
  -- * Calculations
  valueArity, commandType,
  -- * Alpha-equivalence
  (=~=), AlphaEq(..), AlphaEnv, HasId(..)
) where

import {-# SOURCE #-} Language.SequentCore.Translate ( commandToCoreExpr )

import Coercion  ( Coercion, coercionType )
import CoreSyn   ( AltCon(..), Tickish, isRuntimeVar )
import CoreUtils ( exprType )
import DataCon   ( DataCon )
import Id        ( Id, isDataConWorkId_maybe, idArity )
import Literal   ( Literal, litIsTrivial )
import Type      ( Type )
import qualified Type
import Var       ( Var, isId )
import VarEnv

import Data.Maybe

--------------------------------------------------------------------------------
-- AST Types
--------------------------------------------------------------------------------

-- | An atomic value. These include literals, lambdas, and variables, as well as
-- types and coercions (see GHC's 'GHC.Expr' for the reasoning).
data Value b    = Lit Literal       -- ^ A primitive literal value.
                | Var Id            -- ^ A term variable. Must /not/ be a
                                    -- nullary constructor; use 'Cons' for this.
                | Lam b (Command b) -- ^ A function. The body is a computation,
                                    -- that is, a 'Command'.
                | Cons DataCon [Command b]
                                    -- ^ A value formed by a saturated
                                    -- constructor application.
                | Type Type         -- ^ A type. Used to pass a type as an
                                    -- argument to a type-level lambda.
                | Coercion Coercion -- ^ A coercion. Used to pass evidence
                                    -- for the @cast@ operation to a lambda.

-- | A stack frame. A continuation is simply a list of these. Each represents
-- the outer part of a Haskell expression, with a "hole" where a value can be
-- placed. Computation in the sequent calculus is expressed as the interaction
-- of a value with a continuation.
data Frame b    = App  {- expr -} (Command b)    -- ^ Apply the value to an
                                                 -- argument, which may be a
                                                 -- computation.
                | Case {- expr -} b Type [Alt b] -- ^ Perform case analysis on
                                                 -- the value.
                | Cast {- expr -} Coercion       -- ^ Cast the value using the
                                                 -- given proof.
                | Tick (Tickish Id) {- expr -}   -- ^ Annotate the enclosed
                                                 -- frame. Used by the profiler.

-- | A continuation, expressed as a list of 'Frame's. In terms of the sequent
-- calculus, here @nil@ stands for a free covariable; since Haskell does not
-- allow for control effects, we only allow for one covariable.
type Cont b     = [Frame b]

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
data Bind b     = NonRec b (Command b) -- ^ A single non-recursive binding.
                | Rec [(b, Command b)] -- ^ A block of mutually recursive bindings.

-- | A case alternative. Given by the head constructor (or literal), a list of
-- bound variables (empty for a literal), and the body as a 'Command'.
data Alt b      = Alt AltCon [b] (Command b)

-- | Usual instance of 'Value', with 'Var's for binders
type SeqCoreValue   = Value   Var
-- | Usual instance of 'Frame', with 'Var's for binders
type SeqCoreFrame   = Frame   Var
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
mkCommand :: [Bind b] -> Value b -> Cont b -> Command b
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

mkCommand binds val cont
  = Command { cmdLet = binds, cmdValue = val, cmdCont = cont }

-- | Constructs a command that simply returns a value.
valueCommand :: Value b -> Command b
valueCommand v = Command { cmdLet = [], cmdValue = v, cmdCont = [] }

-- | Constructs a command that simply returns a variable.
varCommand :: Id -> Command b
varCommand x = valueCommand (Var x)

-- | Constructs a number of lambdas surrounding a function body.
lambdas :: [b] -> Command b -> Command b
lambdas xs body = foldr (\x c -> valueCommand (Lam x c)) body xs

-- | Adds the given bindings outside those in the given command.
addLets :: [Bind b] -> Command b -> Command b
addLets [] c = c -- avoid unnecessary allocation
addLets bs c = c { cmdLet = bs ++ cmdLet c }

-- | Adds the given continuation frames to the end of those in the given
-- command.
extendCont :: Command b -> Cont b -> Command b
extendCont c fs = c { cmdCont = cmdCont c ++ fs }

--------------------------------------------------------------------------------
-- Deconstructors
--------------------------------------------------------------------------------

-- | Divide a command into a sequence of lambdas and a body. If @c@ is not a
-- lambda, then @collectLambdas c == ([], c)@.
collectLambdas :: Command b -> ([b], Command b)
collectLambdas (Command { cmdLet = [], cmdCont = [], cmdValue = Lam x c })
  = (x : xs, c')
  where (xs, c') = collectLambdas c
collectLambdas c
  = ([], c)

-- | Divide a continuation into a sequence of arguments and an outer
-- continuation. If @k@ is not an application continuation, then
-- @collectArgs k == ([], k)@.
collectArgs :: Cont b -> ([Command b], Cont b)
collectArgs (App c : fs)
  = (c : cs, fs')
  where (cs, fs') = collectArgs fs
collectArgs fs
  = ([], fs)

-- | True if the given command is a simple lambda, with no let bindings and no
-- continuation.
isLambda :: Command b -> Bool
isLambda (Command { cmdLet = [], cmdCont = [], cmdValue = Lam _ _ })
  = True
isLambda _
  = False

-- | True if the given command simply returns a type as a value. This may only
-- be true of a command appearing as an argument (that is, inside an 'App'
-- frame) or as the body of a @let@.
isTypeArg :: Command b -> Bool
isTypeArg (Command { cmdValue = Type _, cmdCont = [], cmdLet = [] }) = True
isTypeArg _ = False

-- | True if the given command simply returns a coercion as a value. This may
-- only be true of a command appearing as an argument (that is, inside an 'App'
-- frame) or as the body of a @let@.
isCoArg :: Command b -> Bool
isCoArg (Command { cmdValue = Type _, cmdCont = [], cmdLet = [] }) = True
isCoArg _ = False

-- | True if the given command simply returns a value that is either a type or
-- a coercion. This may only be true of a command appearing as an argument (that
-- is, inside an 'App' frame) or as the body of a @let@.
isErasedArg :: Command b -> Bool
isErasedArg (Command { cmdValue = v, cmdCont = [] })
  = isErasedValue v
isErasedArg _ = False

-- | True if the given command appears at runtime. Types and coercions are
-- erased.
isRuntimeArg :: Command b -> Bool
isRuntimeArg c = not (isErasedArg c)

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

-- | True if the given value appears at runtime.
isRuntimeValue :: Value b -> Bool
isRuntimeValue v = not (isErasedValue v)

-- | True if the given command represents no actual run-time computation or
-- allocation. For this to hold, it must have no @let@ bindings, and its value
-- and its continuation must both be trivial. Equivalent to
-- 'CoreUtils.exprIsTrivial' in GHC.
isTrivial :: HasId b => Command b -> Bool
isTrivial c
  = null (cmdLet c) &&
      isTrivialCont (cmdCont c) &&
      isTrivialValue (cmdValue c)

-- | True if the given value represents no actual run-time computation. Some
-- literals are not trivial, and a lambda whose argument is not erased or whose
-- body is non-trivial is also non-trivial.
isTrivialValue :: HasId b => Value b -> Bool
isTrivialValue (Lit l)    = litIsTrivial l
isTrivialValue (Lam x c)  = not (isRuntimeVar (identifier x)) && isTrivial c
isTrivialValue _          = True

-- | True if the given continuation represents no actual run-time computation.
-- This holds if all of its frames are trivial (perhaps because it is the empty
-- continuation).
isTrivialCont :: Cont b -> Bool
isTrivialCont = all isTrivialFrame

-- | True if the given continuation represents no actual run-time computation.
-- This is true of casts and of applications of erased arguments (types and
-- coercions). Ticks are not considered trivial, since this would cause them to
-- be inlined.
isTrivialFrame :: Frame b -> Bool
isTrivialFrame (Cast _)   = True
isTrivialFrame (App c)    = isErasedArg c
isTrivialFrame _          = False

-- | If a command represents a saturated call to some function, splits it into
-- the function, the arguments, and the remaining continuation after the
-- arguments.
commandAsSaturatedCall :: Command b -> Maybe (Value b, [Command b], Cont b)
commandAsSaturatedCall c
  = do
    let val = cmdValue c
    (args, cont) <- asSaturatedCall val (cmdCont c)
    return $ (val, args, cont)

-- | If the given value is a function, and the given continuation would provide
-- enough arguments to saturate it, returns the arguments and the remainder of
-- the continuation.
asSaturatedCall :: Value b -> Cont b -> Maybe ([Command b], Cont b)
asSaturatedCall val cont
  | 0 < arity, arity <= length args
  = Just (args, others)
  | otherwise
  = Nothing
  where
    arity = valueArity val
    (args, others) = collectArgs cont

-- | If a command does nothing but provide a value, returns that value.
asValueCommand :: Command b -> Maybe (Value b)
asValueCommand (Command { cmdLet = [], cmdValue = v, cmdCont = [] })
  = Just v
asValueCommand _
  = Nothing

--------------------------------------------------------------------------------
-- Calculations
--------------------------------------------------------------------------------

-- | Compute the type of a command.
commandType :: SeqCoreCommand -> Type
commandType = exprType . commandToCoreExpr -- Cheaty, but effective

-- | Compute (a conservative estimate of) the arity of a value. If the value is
-- a variable, this may be a lower bound.
valueArity :: Value b -> Int
valueArity (Var x)
  | isId x = idArity x
valueArity (Lam _ c)
  = 1 + length xs
  where (xs, _) = collectLambdas c
valueArity _ = 0

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
  aeqIn env (Lam b1 c1) (Lam b2 c2)
    = aeqIn (rnBndr2 env (identifier b1) (identifier b2)) c1 c2
  aeqIn env (Type t1) (Type t2)
    = aeqIn env t1 t2
  aeqIn env (Coercion co1) (Coercion co2)
    = aeqIn env co1 co2
  aeqIn env (Var x1) (Var x2)
    = env `rnOccL` x1 == env `rnOccR` x2
  aeqIn _ _ _
    = False

instance HasId b => AlphaEq (Frame b) where
  aeqIn env (App c1) (App c2)
    = aeqIn env c1 c2
  aeqIn env (Case x1 t1 as1) (Case x2 t2 as2)
    = aeqIn env' t1 t2 && aeqIn env' as1 as2
      where env' = rnBndr2 env (identifier x1) (identifier x2)
  aeqIn env (Cast co1) (Cast co2)
    = aeqIn env co1 co2
  aeqIn _ (Tick ti1) (Tick ti2)
    = ti1 == ti2
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
    alpha :: HasId b => (b, Command b) -> (b, Command b) -> Bool
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
