module Language.SequentCore.Simpl.ExprSize (
  ExprSize(..), valueSize, contSize, commandSize
) where

import Language.SequentCore.Syntax

import Bag
import DataCon
import DynFlags
import Id
import IdInfo
import Literal
import Outputable
import PrelNames ( buildIdKey, augmentIdKey )
import PrimOp
import Type
import TysPrim   ( realWorldStatePrimTy )
import Unique
import Util      ( count )

import qualified Data.ByteString as BS

data ExprSize
  = TooBig
  | ExprSize { esBase :: !Int
             , esArgDiscs :: Bag (Id, Int)
             , esResultDisc :: !Int
             }

instance Outputable ExprSize where
  ppr TooBig = text "TooBig"
  ppr (ExprSize b _ r) = brackets (int b <+> int r)

sizeZero :: ExprSize
sizeZero = ExprSize { esBase = 0, esArgDiscs = emptyBag, esResultDisc = 0 }

sizeN :: Int -> ExprSize
sizeN n = ExprSize { esBase = n, esArgDiscs = emptyBag, esResultDisc = 0 }

maxSize :: ExprSize -> ExprSize -> ExprSize
TooBig               `maxSize` _                    = TooBig
_                    `maxSize` TooBig               = TooBig
s1@(ExprSize b1 _ _) `maxSize` s2@(ExprSize b2 _ _) = if b1 > b2 then s1 else s2

mkExprSize :: Int -> Int -> Bag (Id, Int) -> Int -> ExprSize
mkExprSize cap b as r
  | cap < b - r = TooBig
  | otherwise   = ExprSize { esBase = b, esArgDiscs = as, esResultDisc = r }

valueSize   :: DynFlags -> Int -> [Id] -> SeqCoreValue   -> ExprSize
contSize    :: DynFlags -> Int -> [Id] -> SeqCoreCont    -> ExprSize
commandSize :: DynFlags -> Int -> [Id] -> SeqCoreCommand -> ExprSize

-- We have three mutually recursive functions, but only one argument changes
-- between recursive calls; easiest to use one recursive function that takes
-- a sum

data Expr = V SeqCoreValue | C SeqCoreCommand | K SeqCoreCont

instance Outputable Expr where
  ppr (V val) = ppr val
  ppr (C comm) = ppr comm
  ppr (K cont) = ppr cont

exprSize :: DynFlags -> Int -> [Id] -> Expr -> ExprSize

valueSize   dflags cap topArgs val  = exprSize dflags cap topArgs (V val)
contSize    dflags cap topArgs cont = exprSize dflags cap topArgs (K cont)
commandSize dflags cap topArgs comm = exprSize dflags cap topArgs (C comm)

exprSize dflags cap topArgs expr
  = cap `seq` size expr -- use seq to unbox cap now; we will use it often
  where
    size (V (Type _))       = sizeZero
    size (V (Coercion _))   = sizeZero
    size (V (Var _))        = sizeZero -- invariant: not a nullary constructor
    size (V (Compute comm)) = size (C comm)
    size (V (Cont cont))    = size (K cont)
    size (V (Lit lit))      = sizeN (litSize lit)
    size (V (Cons dc args)) = sizeArgs args `addSizeNSD`
                              sizeCall (dataConWorkId dc) args voids
      where voids           = count isRealWorldValue args
    size (V (Lam x comm))   | erased    = size (C comm)
                            | otherwise = lamScrutDiscount dflags (size (C comm))
      where erased          = isId x && not (isRealWorldId x)
    
    size (K Return)         = sizeZero
    size (K (Jump _))       = sizeZero
    size (K (Cast _ cont))  = size (K cont)
    size (K (Tick _ cont))  = size (K cont)
    size (K (App arg cont)) = sizeArg arg `addSizeNSD` size (K cont)
    size (K (Case _ _ alts cont))
                            = sizeAlts alts `addSizeOfCont` cont

    size (C comm)           = sizeLets (cmdLet comm) `addSizeNSD`
                              sizeCut (cmdValue comm) (cmdCont comm)
    
    sizeCut :: SeqCoreValue -> SeqCoreCont -> ExprSize
    -- Compare this clause to size_up_app in CoreUnfold; already having the
    -- function and arguments at hand avoids some acrobatics
    sizeCut (Var f) cont@(App {})
      = let (args, cont') = collectArgs cont
            realArgs      = filter (not . isErasedValue) args
            voids         = count isRealWorldValue realArgs
        in sizeArgs realArgs `addSizeNSD` sizeCall f realArgs voids
                             `addSizeOfCont` cont'
    sizeCut (Var x) (Case _b _ty alts cont')
      | x `elem` topArgs
      = combineSizes total max `addSizeOfCont` cont'
      where
        altSizes = map sizeAlt alts
        total    = foldr addAltSize sizeZero altSizes
        max      = foldr maxSize    sizeZero altSizes
        
        combineSizes (ExprSize totBase totArgDiscs totResDisc)
                     (ExprSize maxBase _           _)
          = ExprSize totBase
                     (unitBag (x, 20 + totBase - maxBase)
                       `unionBags` totArgDiscs)
                     totResDisc
        combineSizes tot _ = tot -- must be TooBig

    sizeCut val cont
      = size (V val) `addSizeOfCont` cont

    sizeArg :: SeqCoreValue -> ExprSize
    sizeArg arg = size (V arg)

    sizeArgs :: [SeqCoreValue] -> ExprSize
    sizeArgs args = foldr addSizeNSD sizeZero (map sizeArg args)

    -- Lifted from CoreUnfold
    sizeCall :: Id -> [SeqCoreValue] -> Int -> ExprSize
    sizeCall fun valArgs voids
       = case idDetails fun of
           FCallId _        -> sizeN (10 * (1 + length valArgs))
           DataConWorkId dc -> conSize dc (length valArgs)
           PrimOpId op      -> primOpSize op (length valArgs)
           ClassOpId _      -> classOpSize dflags topArgs valArgs
           _                -> funSize dflags topArgs fun (length valArgs) voids

    sizeAlt :: SeqCoreAlt -> ExprSize
    sizeAlt (Alt _ _ rhs) = size (C rhs) `addSizeN` 10

    sizeAlts :: [SeqCoreAlt] -> ExprSize
    sizeAlts alts = foldr addAltSize sizeZero (map sizeAlt alts)

    sizeBind :: SeqCoreBind -> ExprSize
    sizeBind (NonRec x rhs)
      = size (V rhs) `addSizeN` allocSize
      where
        allocSize
          -- An unlifted type has no heap allocation
          | isUnLiftedType (idType x) =  0
          | otherwise                 = 10

    sizeBind (Rec pairs)
      = foldr (addSizeNSD . pairSize) (sizeN allocSize) pairs
      where
        allocSize                     = 10 * length pairs
        pairSize (_x, rhs)            = size (V rhs)

    sizeLets :: [SeqCoreBind] -> ExprSize
    sizeLets binds = foldr (addSizeNSD . sizeBind) sizeZero binds

    addSizeN :: ExprSize -> Int -> ExprSize
    addSizeN TooBig            _ = TooBig
    addSizeN (ExprSize b as r) d = mkExprSize cap (b + d) as r

    -- How to combine the sizes of alternatives
    addAltSize :: ExprSize -> ExprSize -> ExprSize
    addAltSize (ExprSize b1 as1 r1) (ExprSize b2 as2 r2)
      = mkExprSize cap (b1 + b2) (as1 `unionBags` as2) (r1 + r2)
    addAltSize _ _ = TooBig

    -- ignores the result discount on the LEFT argument
    addSizeNSD :: ExprSize -> ExprSize -> ExprSize
    addSizeNSD TooBig _      = TooBig
    addSizeNSD _      TooBig = TooBig
    addSizeNSD (ExprSize b1 as1 _) (ExprSize b2 as2 r2)
      = mkExprSize cap (b1 + b2) (as1 `unionBags` as2) r2

    -- If a continuation passes the value through unchanged, then it should not
    -- count against the result discount (and has size zero anyway).
    addSizeOfCont :: ExprSize -> SeqCoreCont -> ExprSize
    addSizeOfCont size1 cont
      | isPassThroughCont cont = size1
      | otherwise              = size1 `addSizeNSD` size (K cont)

    isPassThroughCont :: Cont b -> Bool
    isPassThroughCont Return         = True
    isPassThroughCont (Tick _ cont)  = isPassThroughCont cont
    isPassThroughCont (Cast _ cont)  = isPassThroughCont cont
    isPassThroughCont (App arg cont) = isErasedValue arg
                                         && isPassThroughCont cont
    isPassThroughCont _              = False

    infixl 6 `addSizeN`, `addSizeNSD`, `addSizeOfCont`

-- Lifted from CoreUnfold
litSize :: Literal -> Int
litSize (LitInteger {}) = 100	-- Note [Size of literal integers]
litSize (MachStr str)   = 10 + 10 * ((BS.length str + 3) `div` 4)
  -- If size could be 0 then @f "x"@ might be too small
  -- [Sept03: make literal strings a bit bigger to avoid fruitless 
  --  duplication of little strings]
litSize _other = 0    -- Must match size of nullary constructors
                      -- Key point: if  x |-> 4, then x must inline unconditionally
                      --     	    (eg via case binding)

-- Lifted from CoreUnfold
classOpSize :: DynFlags -> [Id] -> [SeqCoreValue] -> ExprSize
-- See Note [Conlike is interesting]
classOpSize _ _ []
  = sizeZero
classOpSize dflags top_args (arg1 : other_args)
  = ExprSize size arg_discount 0
  where
    size = 20 + (10 * length other_args)
    -- If the class op is scrutinising a lambda bound dictionary then
    -- give it a discount, to encourage the inlining of this function
    -- The actual discount is rather arbitrarily chosen
    arg_discount = case arg1 of
                     Var dict | dict `elem` top_args 
                              -> unitBag (dict, ufDictDiscount dflags)
                     _other   -> emptyBag
    		     
-- Lifted from CoreUnfold
funSize :: DynFlags -> [Id] -> Id -> Int -> Int -> ExprSize
-- Size for functions that are not constructors or primops
-- Note [Function applications]
funSize dflags top_args fun n_val_args voids
  | fun `hasKey` buildIdKey   = buildSize
  | fun `hasKey` augmentIdKey = augmentSize
  | otherwise = ExprSize size arg_discount res_discount
  where
    some_val_args = n_val_args > 0

    size | some_val_args = 10 * (1 + n_val_args - voids)
         | otherwise     = 0
        -- The 1+ is for the function itself
        -- Add 1 for each non-trivial arg;
        -- the allocation cost, as in let(rec)
  
        --                  DISCOUNTS
        --  See Note [Function and non-function discounts]
    arg_discount | some_val_args && fun `elem` top_args
                 = unitBag (fun, ufFunAppDiscount dflags)
                 | otherwise = emptyBag
        -- If the function is an argument and is applied
        -- to some values, give it an arg-discount

    res_discount | idArity fun > n_val_args = ufFunAppDiscount dflags
                 | otherwise                = 0
        -- If the function is partially applied, show a result discount

-- Lifted from CoreUnfold
primOpSize :: PrimOp -> Int -> ExprSize
primOpSize op n_val_args
 = if primOpOutOfLine op
      then sizeN (op_size + n_val_args)
      else sizeN op_size
 where
   op_size = primOpCodeSize op

-- Lifted from CoreUnfold
buildSize :: ExprSize
buildSize = ExprSize 0 emptyBag 40
  -- We really want to inline applications of build
  -- build t (\cn -> e) should cost only the cost of e (because build will be inlined later)
  -- Indeed, we should add a result_discount becuause build is 
  -- very like a constructor.  We don't bother to check that the
  -- build is saturated (it usually is).  The "-2" discounts for the \c n, 
  -- The "4" is rather arbitrary.

-- Lifted from CoreUnfold
augmentSize :: ExprSize
augmentSize = ExprSize 0 emptyBag 40
  -- Ditto (augment t (\cn -> e) ys) should cost only the cost of
  -- e plus ys. The -2 accounts for the \cn 

-- Lifted from CoreUnfold
conSize :: DataCon -> Int -> ExprSize
conSize dc n_val_args
  | n_val_args == 0      = ExprSize  0 emptyBag 10    -- Like variables

-- See Note [Unboxed tuple size and result discount]
  | isUnboxedTupleCon dc = ExprSize  0 emptyBag (10 * (1 + n_val_args))

-- See Note [Constructor size and result discount]
  | otherwise            = ExprSize 10 emptyBag (10 * (1 + n_val_args))

lamScrutDiscount :: DynFlags -> ExprSize -> ExprSize
lamScrutDiscount _      TooBig = TooBig
lamScrutDiscount dflags (ExprSize b as _)
  = ExprSize b as (ufFunAppDiscount dflags)

isRealWorldId :: Id -> Bool
isRealWorldId id = idType id `eqType` realWorldStatePrimTy

isRealWorldValue :: Value b -> Bool
-- an expression of type State# RealWorld must be a variable
isRealWorldValue (Var id) = isRealWorldId id
isRealWorldValue _        = False

