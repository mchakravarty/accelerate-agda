{-# LANGUAGE GADTs, TypeOperators #-}
module Accel
  (Array,
   EltDict(..), eltDictZZ, eltDictZC, eltDictBool, eltDictInt, eltDictFloat, eltDictDouble, eltDictPair, 
   IsNumDict(..), isNumDictInt, isNumDictFloat, isNumDictDouble,
   ReadDict(..), readDictBool, readDictInt, readDictFloat, readDictDouble,
   SizedShapeDict(..), sizedShapeDictZ, sizedShapeDictC,
   ShapeDict(..), shapeDictZ, shapeDictC,
   IsScalarDict(..), isScalarDictBool, isScalarDictInt, isScalarDictDouble, isScalarDictFloat,
   IsIntegralDict(..), isIntegralDictInt,
   BitsDict(..), bitsDictInt,
   constantInt, constantFloat, constantDouble, constantFromString, valFromString,
   constant, mkAdd, mkSub, mkMul, mkAbs, mkIte, mkBXor, mkShiftR,
   fromList, fromList', toList, showArray,
   use, run, generate, fold, fold1, Accel.scanl, scanl', Accel.scanl1, prescanl, prescanr, permute, backpermute,
   Accel.zipWith, Accel.zip, Accel.map, the, (!),
   Accel.fst, Accel.snd, Accel.pair
  ) where

import qualified Data.Bits as B 
import qualified Data.Array.Accelerate as A
import qualified Data.Array.Accelerate.Interpreter as Interpreter
import qualified Data.Array.Accelerate.Smart as Smart
import Unsafe.Coerce

-- element dictionaries -- needed for array element types
data EltDict e where
  EltDict :: (A.Elt e) => EltDict e

eltDictZZ :: EltDict A.Z
eltDictZZ = EltDict

eltDictZC :: EltDict sh -> EltDict ix -> EltDict ((A.:.) sh ix)
eltDictZC EltDict EltDict = EltDict

eltDictPair :: EltDict a -> EltDict b -> EltDict (a, b)
eltDictPair EltDict EltDict = EltDict

eltDictBool :: EltDict Bool
eltDictBool = EltDict

eltDictInt :: EltDict Int
eltDictInt = EltDict

eltDictFloat :: EltDict Float
eltDictFloat = EltDict

eltDictDouble :: EltDict Double
eltDictDouble = EltDict

-- numeric dictionaries -- needed for Exp types
data IsNumDict e where
  IsNumDict :: (A.IsNum e) => IsNumDict e

isNumDictInt :: IsNumDict Int
isNumDictInt = IsNumDict

isNumDictFloat :: IsNumDict Float
isNumDictFloat = IsNumDict

isNumDictDouble :: IsNumDict Double
isNumDictDouble = IsNumDict

-- read dictionaries -- needed for constants
data ReadDict e where
  ReadDict :: Read e => ReadDict e

readDictBool :: ReadDict Bool
readDictBool = ReadDict

readDictInt :: ReadDict Int
readDictInt = ReadDict

readDictFloat :: ReadDict Float
readDictFloat = ReadDict

readDictDouble :: ReadDict Double
readDictDouble = ReadDict

-- integral dictionaries -- needed for comparisons
data IsIntegralDict e where
  IsIntegralDict :: A.IsIntegral e => IsIntegralDict e

isIntegralDictInt :: IsIntegralDict Int
isIntegralDictInt = IsIntegralDict

-- bits dictionaries -- needed for bit operations
data BitsDict e where
  BitsDict :: (A.IsIntegral e, B.Bits e) => BitsDict e

bitsDictInt :: BitsDict Int
bitsDictInt = BitsDict

-- scalar dictionaries -- needed for comparisons
data IsScalarDict e where
  IsScalarDict :: A.IsScalar e => IsScalarDict e

isScalarDictBool :: IsScalarDict Bool
isScalarDictBool = IsScalarDict

isScalarDictInt :: IsScalarDict Int
isScalarDictInt = IsScalarDict

isScalarDictFloat :: IsScalarDict Float
isScalarDictFloat = IsScalarDict

isScalarDictDouble :: IsScalarDict Double
isScalarDictDouble = IsScalarDict

-- sized shape dictionaries
data SizedShapeDict sh where
  SizedShapeDict :: (A.Slice sh, A.Shape sh) => A.Exp sh -> SizedShapeDict sh

sizedShapeDictZ :: SizedShapeDict A.Z
sizedShapeDictZ = SizedShapeDict (A.lift A.Z)

sizedShapeDictC :: Int -> SizedShapeDict sh -> SizedShapeDict ((A.:.) sh Int)
sizedShapeDictC n (SizedShapeDict esh) = SizedShapeDict (A.lift ((A.:.) esh n))

-- shape dictionaries -- needed for reshaping arrays
data ShapeDict sh where
  ShapeDict :: A.Shape sh => ShapeDict sh

shapeDictZ :: ShapeDict A.Z
shapeDictZ = ShapeDict

shapeDictC :: ShapeDict sh -> ShapeDict ((A.:.) sh Int)
shapeDictC ShapeDict = ShapeDict

data SHAPE where
  SHAPE :: A.Shape sh => sh -> SHAPE

dim :: [Int] -> SHAPE
dim [] = SHAPE A.Z
dim [x1] = SHAPE (A.Z A.:. x1)
dim [x1,x2] = SHAPE (A.Z A.:. x1 A.:. x2)
dim [x1,x2,x3] = SHAPE (A.Z A.:. x1 A.:. x2 A.:. x3)
dim [x1,x2,x3,x4] = SHAPE (A.Z A.:. x1 A.:. x2 A.:. x3 A.:. x4)
dim [x1,x2,x3,x4,x5] = SHAPE (A.Z A.:. x1 A.:. x2 A.:. x3 A.:. x4 A.:. x5)
dim [x1,x2,x3,x4,x5,x6] = SHAPE (A.Z A.:. x1 A.:. x2 A.:. x3 A.:. x4 A.:. x5 A.:. x6)

-- wrapper type for arrays
-- internally everything is viewed as a one-dimensional array
newtype Array index elem = ARRAY (A.Array A.DIM1 elem)

instance Show (Array index e) where
  showsPrec i (ARRAY ar) = showsPrec i ar

fromList :: EltDict e
         -> [e] 
         -> Array ix e
fromList EltDict es = ARRAY (A.fromList ((A.:.) A.Z (length es)) es)

fromList' :: A.Elt e
         => [e] 
         -> Array ix e
fromList' es = ARRAY (A.fromList ((A.:.) A.Z (length es)) es)

toList :: Array ix e 
       -> [e]
toList (ARRAY ar) = A.toList ar

showArray :: EltDict e
          -> Array ix e
          -> String
showArray EltDict (ARRAY ar) = show ar

use :: EltDict e
    -> Array A.DIM1 e
    -> A.Acc (A.Array A.DIM1 e)
use EltDict (ARRAY ar) = (A.use ar)

run :: EltDict e
    -> A.Acc (A.Array A.DIM1 e)
    -> Array A.DIM1 e
run EltDict (acc_ar) = ARRAY (Interpreter.run (unsafeCoerce acc_ar))

generate :: EltDict a
         -> SizedShapeDict ix
         -> (A.Exp ix -> A.Exp a)
         -> A.Acc (A.Array A.DIM1 a)
generate EltDict (SizedShapeDict sh) f =
  let
    result = A.generate sh f
  in
    A.reshape (A.lift (A.Z A.:. (A.size result))) result

fold :: EltDict a
     -> Int -> Int
     -> (A.Exp a -> A.Exp a -> A.Exp a)
     -> A.Exp a
     -> A.Acc (A.Array A.DIM1 a)
     -> A.Acc (A.Array A.DIM1 a)
fold EltDict size2 size1 f e a =
     (A.reshape (A.lift (A.Z A.:. size2))
      (A.fold f e
       (A.reshape (A.lift (A.Z A.:. size2 A.:. size1)) a)))

fold1 :: EltDict a
     -> Int -> Int
     -> (A.Exp a -> A.Exp a -> A.Exp a)
     -> A.Acc (A.Array A.DIM1 a)
     -> A.Acc (A.Array A.DIM1 a)
fold1 EltDict size2 size1 f a =
     (A.reshape (A.lift (A.Z A.:. size2))
      (A.fold1 f
       (A.reshape (A.lift (A.Z A.:. size2 A.:. size1)) a)))

prescanl EltDict f e a =
  A.prescanl f e a

prescanr EltDict f e a =
  A.prescanr f e a

prescanr, prescanl, scanl :: EltDict a
      -> (A.Exp a -> A.Exp a -> A.Exp a)
      -> A.Exp a
      -> A.Acc (A.Array A.DIM1 a)
      -> A.Acc (A.Array A.DIM1 a)
scanl EltDict f e a =
  A.scanl f e a

scanl' :: EltDict a
       -> (A.Exp a -> A.Exp a -> A.Exp a)
       -> A.Exp a
       -> A.Acc (A.Array A.DIM1 a)
       -> (A.Acc (A.Array A.DIM1 a), A.Acc (A.Array A.DIM0 a))
scanl' EltDict f e a = 
  A.scanl' f e a

scanl1 :: EltDict a
       -> (A.Exp a -> A.Exp a -> A.Exp a)
       -> A.Acc (A.Array A.DIM1 a)
       -> A.Acc (A.Array A.DIM1 a)
scanl1 EltDict f a =
  A.scanl1 f a

permute :: EltDict a
        -> SizedShapeDict ixarg
        -> SizedShapeDict ixres
        -> (A.Exp a -> A.Exp a -> A.Exp a)
        -> A.Acc (A.Array A.DIM1 a)
        -> (A.Exp ixarg -> A.Exp ixres)
        -> A.Acc (A.Array A.DIM1 a)
        -> A.Acc (A.Array A.DIM1 a)
permute EltDict (SizedShapeDict arg_shape) (SizedShapeDict result_shape) f def tr a =
  let
    result = A.permute f (A.reshape result_shape def) tr (A.reshape arg_shape a)
  in
    A.reshape (A.lift (A.Z A.:. (A.size result))) result

backpermute :: EltDict a
            -> SizedShapeDict ixarg
            -> ShapeDict ixres
            -> A.Exp ixres
            -> (A.Exp ixres -> A.Exp ixarg)
            -> A.Acc (A.Array A.DIM1 a)
            -> A.Acc (A.Array A.DIM1 a)
backpermute EltDict (SizedShapeDict arg_shape) ShapeDict result_shape f a =
  let
    result = A.backpermute result_shape f (A.reshape arg_shape a)
  in
    A.reshape (A.lift (A.Z A.:. (A.size result))) result

(!) :: EltDict a
    -> SizedShapeDict ix
    -> A.Acc (A.Array A.DIM1 a)
    -> A.Exp ix
    -> A.Exp a
(!) EltDict (SizedShapeDict ix_sh) a ix =
  (A.!) (A.reshape ix_sh a) ix

zip :: EltDict a
        -> EltDict b
        -> A.Acc (A.Array A.DIM1 a)
        -> A.Acc (A.Array A.DIM1 b)
        -> A.Acc (A.Array A.DIM1 (a, b))
zip EltDict EltDict a b = A.zip a b

zipWith :: EltDict a
        -> EltDict b
        -> EltDict c
        -> (A.Exp a -> A.Exp b -> A.Exp c)
        -> A.Acc (A.Array A.DIM1 a)
        -> A.Acc (A.Array A.DIM1 b)
        -> A.Acc (A.Array A.DIM1 c)
zipWith EltDict EltDict EltDict f a b = A.zipWith f a b

map :: EltDict a
    -> EltDict b
    -> (A.Exp a -> A.Exp b)
    -> A.Acc (A.Array A.DIM1 a)
    -> A.Acc (A.Array A.DIM1 b)
map EltDict EltDict f a = A.map f a

the :: EltDict e
    -> A.Acc (A.Array A.DIM1 e)
    -> A.Exp e
the EltDict a = A.the (A.reshape (A.lift A.Z) a)

mkAdd :: EltDict a
      -> IsNumDict a
      -> A.Exp a 
      -> A.Exp a
      -> A.Exp a
mkAdd EltDict IsNumDict x y = Smart.mkAdd x y

mkSub :: EltDict a
      -> IsNumDict a
      -> A.Exp a 
      -> A.Exp a
      -> A.Exp a
mkSub EltDict IsNumDict x y = Smart.mkSub x y

mkMul :: EltDict a
      -> IsNumDict a
      -> A.Exp a 
      -> A.Exp a
      -> A.Exp a
mkMul EltDict IsNumDict x y = Smart.mkMul x y

mkAbs :: EltDict a
      -> IsNumDict a
      -> A.Exp a 
      -> A.Exp a
mkAbs EltDict IsNumDict x = Smart.mkAbs x

mkIte :: EltDict a
      -> A.Exp Bool
      -> A.Exp a
      -> A.Exp a
      -> A.Exp a
mkIte EltDict b t e = (A.?) b (t, e)

mkBXor :: EltDict a
       -> IsIntegralDict a
       -> A.Exp a
       -> A.Exp a
       -> A.Exp a
mkBXor EltDict IsIntegralDict x y = Smart.mkBXor x y

mkBitAnd :: EltDict a
         -> BitsDict a
         -> A.Exp a
         -> A.Exp a
         -> A.Exp a
mkBitAnd EltDict BitsDict x y = (B..&.) x y

mkShiftR :: EltDict a
         -> IsIntegralDict a
         -> A.Exp a
         -> A.Exp Int
         -> A.Exp a
mkShiftR EltDict IsIntegralDict x y = A.shiftR x y

fst :: EltDict a
    -> EltDict b
    -> A.Exp (a, b)
    -> A.Exp a
fst EltDict EltDict p = A.fst p

snd :: EltDict a
    -> EltDict b
    -> A.Exp (a, b)
    -> A.Exp b
snd EltDict EltDict p = A.snd p

pair :: EltDict a
     -> EltDict b
     -> A.Exp a
     -> A.Exp b
     -> A.Exp (a, b)
pair EltDict EltDict ea eb = A.lift (ea, eb)

constant :: EltDict a 
         -> a
         -> A.Exp a
constant EltDict a = A.constant a

constantInt :: String
            -> A.Exp Int
constantInt xs = A.constant (read xs)

constantFloat :: String
              -> A.Exp Float
constantFloat xs = A.constant (read xs)

constantDouble :: String
              -> A.Exp Double
constantDouble xs = A.constant (read xs)

constantFromString :: EltDict a
                   -> ReadDict a
                   -> String
                   -> A.Exp a
constantFromString EltDict ReadDict xs = A.constant (read xs)

valFromString :: ReadDict a
              -> String
              -> a
valFromString ReadDict xs = read xs
