{-# LANGUAGE ParallelListComp #-}
-- |
-- Module      : Language.SequentCore.Ops
-- Description : Useful operations on Sequent Core syntax
-- Maintainer  : maurerl@cs.uoregon.edu
-- Stability   : experimental

module Language.SequentCore.Ops (
  -- * Computations
  collectLambdas, isLambda, isSaturatedCtorApp,
  isTypeArg, isCoArg, isErasedArg, isRuntimeArg,
  isTypeValue, isCoValue, isErasedValue, isRuntimeValue,
  isTrivial, isTrivialValue, isTrivialCont, isTrivialFrame,
  saturatedCall, saturatedCtorApp, asValueCommand,
  valueArity, commandType,
  -- * Alpha-equivalence
  (=~=), AlphaEq(..), AlphaEnv, HasId(..)
) where

import Language.SequentCore.Syntax

import Id         ( isDataConId_maybe )
import IdInfo     ( arityInfo )
import Coercion   ( coercionType, Coercion )
import CoreSyn    ( isRuntimeVar )
import CoreUtils  ( exprType )
import Literal    ( litIsTrivial )
import Type       ( Type )
import Var        ( Id, Var, idInfo, isId )
import VarEnv

import Data.Maybe

import qualified Type

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

-- | True if the given command is a saturated application of a constructor. In
-- other words, true if it is @\<Ctor | $ a_1; $ a_2; $ ...; $ a_n; ...>@ for
-- some constructor @Ctor@ with arity @n@.
isSaturatedCtorApp :: Command b -> Bool
isSaturatedCtorApp c@(Command { cmdLet = [], cmdValue = Var x })
  | Just _ <- isDataConId_maybe x
  , Just _ <- saturatedCall c
  = True
isSaturatedCtorApp _
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

isTrivial :: HasId b => Command b -> Bool
isTrivial c
  = null (cmdLet c) &&
      isTrivialCont (cmdCont c) &&
      isTrivialValue (cmdValue c)

isTrivialValue :: HasId b => Value b -> Bool
isTrivialValue (Lit l)    = litIsTrivial l
isTrivialValue (Lam x c)  = not (isRuntimeVar (identifier x)) && isTrivial c
isTrivialValue _          = True

isTrivialCont :: Cont b -> Bool
isTrivialCont = all isTrivialFrame

isTrivialFrame :: Frame b -> Bool
isTrivialFrame (Cast _)   = True
isTrivialFrame (App c)    = isErasedArg c
isTrivialFrame _          = False

-- | If a command represents a saturated call to some function, splits it into
-- the function, the arguments, and the remaining continuation after the
-- arguments.
saturatedCall :: Command b -> Maybe (Value b, [Command b], Cont b)
saturatedCall (Command { cmdValue = v, cmdCont = fs })
  | 0 < arity, arity <= length args
  = Just (v, args, others)
  | otherwise
  = Nothing
  where
    arity = valueArity v

    (args, others) = go fs
    go (App a : fs') = (a : as', fs'') where (as', fs'') = go fs'
    go fs' = ([], fs')

-- TODO We should consider making a saturated constructor invocation a kind of
-- Value. It would make case-of-known-case a shallow pattern-match, for
-- instance.

-- | If a command represents a saturated application of a constructor, splits it
-- into the constructor's identifier, the arguments, and the remaining
-- continuation after the constructor.
saturatedCtorApp :: Command b -> Maybe (Var, [Command b], Cont b)
saturatedCtorApp c
  = do
    (Var fn, args, fs') <- saturatedCall c
    _ <- isDataConId_maybe fn
    return (fn, args, fs')

-- | Compute the type of a command.
commandType :: SeqCoreCommand -> Type
commandType = exprType . commandToCoreExpr -- Cheaty, but effective

-- | Compute (a conservative estimate of) the arity of a value. If the value is
-- a variable, this may be a lower bound.
valueArity :: Value b -> Int
valueArity (Var x)
  | isId x = arityInfo (idInfo x)
valueArity (Lam _ c)
  = 1 + length xs
  where (xs, _) = collectLambdas c
valueArity _ = 0

asValueCommand :: Command b -> Maybe (Value b)
asValueCommand (Command { cmdLet = [], cmdValue = v, cmdCont = [] })
  = Just v
asValueCommand _
  = Nothing

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
