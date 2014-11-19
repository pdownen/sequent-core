{-# LANGUAGE PatternGuards, ParallelListComp #-}

module Language.SequentCore.Ops (
  collectLambdas, isLambda, isSaturatedCtorApp,
  isTypeArg, isNontermArg, isTypeValue, isNontermValue,
  saturatedCall, saturatedCtorApp,
  valueArity, commandType,
  (=~), HasId(..)
) where

import Language.SequentCore.Syntax

import Id (isDataConId_maybe)
import IdInfo (arityInfo)
import Coercion (coercionType, Coercion)
import CoreUtils (exprType)
import Type (Type)
import Var (Id, Var, idInfo, isId)

import qualified Type

import Data.Map (Map)

import qualified Data.Map.Strict as Map

collectLambdas :: Command b -> ([b], Command b)
collectLambdas (Command { cmdLet = [], cmdCont = [], cmdValue = Lam x c })
  = (x : xs, c')
  where (xs, c') = collectLambdas c
collectLambdas c
  = ([], c)

isLambda :: Command b -> Bool
isLambda (Command { cmdLet = [], cmdCont = [], cmdValue = Lam _ _ })
  = True
isLambda _
  = False

isSaturatedCtorApp :: Command b -> Bool
isSaturatedCtorApp (Command { cmdLet = [], cmdValue = v@(Var x)
                            , cmdCont = fs@(App _ : _) })
  | Just _ <- isDataConId_maybe x
  , Just _ <- saturatedCall v fs
  = True
isSaturatedCtorApp _
  = False

isTypeArg :: Command b -> Bool
isTypeArg (Command { cmdValue = Type _, cmdCont = [] }) = True
isTypeArg _ = False

isNontermArg :: Command b -> Bool
isNontermArg (Command { cmdValue = v, cmdCont = [] })
  = isNontermValue v
isNontermArg _ = False

isTypeValue :: Value b -> Bool
isTypeValue (Type _) = True
isTypeValue _ = False

isNontermValue :: Value b -> Bool
isNontermValue (Type _) = True
isNontermValue (Coercion _) = True
isNontermValue _ = False

-- TODO Make types of functions consistent
saturatedCall :: Value b -> Cont b -> Maybe ([Command b], Cont b)
saturatedCall v fs
  | 0 < arity, arity <= length args
  = Just ans
  | otherwise
  = Nothing
  where
    arity = valueArity v

    (args, _) = ans
    ans = go fs []
    go (App c : fs') acc = go fs' (c : acc)
    go fs' acc = (reverse acc, fs')

-- TODO We should consider making a saturated constructor invocation a kind of
-- Value. It would make case-of-known-case a shallow pattern-match, for
-- instance.
saturatedCtorApp :: Command b -> Maybe (Value b, [Command b], Cont b)
saturatedCtorApp (Command { cmdValue = v@(Var fn), cmdCont = fs })
  | Just (args, fs') <- saturatedCall v fs
  , Just _ <- isDataConId_maybe fn
  = Just (v, args, fs')
saturatedCtorApp _ = Nothing

commandType :: SeqCoreCommand -> Type
commandType = exprType . commandToCoreExpr

valueArity :: Value b -> Int
valueArity (Var x)
  | isId x = arityInfo (idInfo x)
valueArity (Lam _ c)
  = 1 + length xs
  where (xs, _) = collectLambdas c
valueArity _ = 0

class HasId a where
  identifier :: a -> Id

instance HasId Var where
  identifier x = x

type AlphaEnv = Map Id Id

class AlphaEq a where
  alphaIn :: AlphaEnv -> a -> a -> Bool

(=~) :: AlphaEq a => a -> a -> Bool
(=~) = alphaIn Map.empty

instance HasId b => AlphaEq (Value b) where
  alphaIn _ (Lit l1) (Lit l2)
    = l1 == l2
  alphaIn env (Lam b1 c1) (Lam b2 c2)
    = alphaIn (Map.insert (identifier b1) (identifier b2) env) c1 c2
  alphaIn env (Type t1) (Type t2)
    = alphaIn env t1 t2
  alphaIn env (Coercion co1) (Coercion co2)
    = alphaIn env co1 co2
  alphaIn env (Var x1) (Var x2)
    | Just x' <- Map.lookup x1 env = x' == x2
    | otherwise = x1 == x2 -- free variable; must be equal
  alphaIn _ _ _
    = False

instance HasId b => AlphaEq (Frame b) where
  alphaIn env (App c1) (App c2)
    = alphaIn env c1 c2
  alphaIn env (Case x1 t1 as1) (Case x2 t2 as2)
    = alphaIn env' t1 t2 && alphaIn env' as1 as2
      where env' = Map.insert (identifier x1) (identifier x2) env
  alphaIn env (Cast co1) (Cast co2)
    = alphaIn env co1 co2
  alphaIn _ (Tick ti1) (Tick ti2)
    = ti1 == ti2
  alphaIn _ _ _
    = False

instance HasId b => AlphaEq (Command b) where
  alphaIn env 
    (Command { cmdLet = bs1, cmdValue = v1, cmdCont = c1 })
    (Command { cmdLet = bs2, cmdValue = v2, cmdCont = c2 })
    | Just env' <- alphaBindsIn env bs1 bs2
    = alphaIn env' v1 v2 && alphaIn env' c1 c2
    | otherwise
    = False

alphaBindsIn :: HasId b => AlphaEnv -> [Bind b] -> [Bind b] -> Maybe AlphaEnv
alphaBindsIn env [] []
  = Just env
alphaBindsIn env (b1:bs1) (b2:bs2)
  = alphaBindIn env b1 b2 >>= \env' -> alphaBindsIn env' bs1 bs2
alphaBindsIn _ _ _
  = Nothing

alphaBindIn :: HasId b => AlphaEnv -> Bind b -> Bind b -> Maybe AlphaEnv
alphaBindIn env (NonRec x1 c1) (NonRec x2 c2)
  = if alphaIn env' c1 c2 then Just env' else Nothing
  where env' = Map.insert (identifier x1) (identifier x2) env
alphaBindIn env (Rec bs1) (Rec bs2)
  = if and $ zipWith alpha bs1 bs2 then Just env' else Nothing
  where
    alpha :: HasId b => (b, Command b) -> (b, Command b) -> Bool
    alpha (_, c1) (_, c2)
      = alphaIn env' c1 c2
    env'
      = Map.fromList [ (identifier x1, identifier x2) | (x1, _) <- bs1
                                                      | (x2, _) <- bs2 ]
          `Map.union` env
alphaBindIn _ _ _
  = Nothing

instance HasId b => AlphaEq (Alt b) where
  alphaIn env (Alt a1 xs1 c1) (Alt a2 xs2 c2)
    = a1 == a2 && alphaIn env' c1 c2
    where
      env' = Map.fromList (zip is1 is2) `Map.union` env
      is1  = map identifier xs1
      is2  = map identifier xs2

instance AlphaEq Type where
  alphaIn env t1 t2
    | Just x1 <- Type.getTyVar_maybe t1
    , Just x2 <- Type.getTyVar_maybe t2
    = x1 == x2
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
    = alphaIn (Map.insert x1 x2 env) t1' t2'
    | otherwise
    = False
    where
      alpha a1 a2 = alphaIn env a1 a2

instance AlphaEq Coercion where
  -- Consider coercions equal if their types are equal (proof irrelevance)
  alphaIn env co1 co2 = alphaIn env (coercionType co1) (coercionType co2)
    

instance AlphaEq a => AlphaEq [a] where
  alphaIn env xs ys = and $ zipWith (alphaIn env) xs ys
