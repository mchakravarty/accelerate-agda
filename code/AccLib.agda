module AccLib where

{-# IMPORT Data.Array.Accelerate #-}
{-# IMPORT Data.Array.Accelerate.Smart #-}
{-# IMPORT Accel #-}

open import Data.Bool using (true; false; T) renaming (Bool to AgBool)
open import Data.Empty
open import Data.List hiding ([_]; zipWith; zip; map; scanl)
open import Data.Nat using (ℕ; suc; zero; _>_) renaming (_*_ to _*ℕ_)
open import Data.Product hiding (zip; map) renaming (_,_ to _,,_)
open import Data.String hiding (_==_)
open import Data.Unit
open import Data.Vec hiding ([_]; zipWith; zip) renaming (map to vmap)

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import Parsing using (isBoolLiteral; isIntLiteral; isFloatLiteral)

data Slice : ℕ → AgBool → Set where
  Z     : Slice 0 false
  Any   : Slice 0 true
  _:<_> : ∀ {m n} → Slice m n → ℕ → Slice m n
  _:All : ∀ {m n} → Slice m n → Slice (suc m) n

Shape = Slice 0 false

[_] = _:<_> Z
[_,_] : ℕ → ℕ → Shape
[ m , n ] = [ m ] :< n >
[_,_,_] : ℕ → ℕ → ℕ → Shape
[ m , n , o ] = [ m , n ] :< o >

size : Shape → ℕ
size Z = 1
size (sh :< n >) = size sh *ℕ n

postulate
  HsArray : Set → Set → Set
  HsEltDict : Set → Set
  HsIsScalarDict : Set → Set
  HsIsIntegralDict : Set → Set
  HsShapeDict : Set → Set
  HsSizedShapeDict : Set → Set
  HsIsNumDict : Set → Set
  HsReadDict : Set → Set
  HsBitsDict : Set → Set
  AccArray : Set → Set → Set
  Acc : Set → Set
  AccExp : Set → Set
  HsDIM0 : Set
  HsDIM1 : Set
  HsDIM2 : Set
  HsDIM3 : Set
  HsPair : Set → Set → Set
  fstHs : ∀ {A B} → HsPair A B → A
  sndHs : ∀ {A B} → HsPair A B → B
  HsZ : Set
  HsC : Set → Set → Set
  HsBool : Set
  HsInt : Set
  HsFloat : Set
  HsDouble : Set
  eltDictZZ : HsEltDict HsZ
  eltDictZC : ∀ {A B} → HsEltDict A → HsEltDict B → HsEltDict (HsC A B)
  eltDictBool : HsEltDict HsBool
  eltDictInt : HsEltDict HsInt
  eltDictFloat : HsEltDict HsFloat
  eltDictDouble : HsEltDict HsDouble
  eltDictPair : ∀ {A B} → HsEltDict A → HsEltDict B → HsEltDict (HsPair A B)
  isNumDictInt : HsIsNumDict HsInt
  isNumDictFloat : HsIsNumDict HsFloat
  isNumDictDouble : HsIsNumDict HsDouble
  bitsDictInt : HsBitsDict HsInt
  readDictBool : HsReadDict HsBool
  readDictInt : HsReadDict HsInt
  readDictFloat : HsReadDict HsFloat
  readDictDouble : HsReadDict HsDouble
  shapeDictZ : HsShapeDict HsZ
  shapeDictC : ∀ {sh} → HsShapeDict sh → HsShapeDict (HsC sh HsInt)
  sizedShapeDictZ : HsSizedShapeDict HsZ
  sizedShapeDictC : ∀ {sh} → HsInt → HsSizedShapeDict sh → HsSizedShapeDict (HsC sh HsInt)
  isScalarDictBool : HsIsScalarDict HsBool
  isScalarDictInt : HsIsScalarDict HsInt
  isScalarDictFloat : HsIsScalarDict HsFloat
  isScalarDictDouble : HsIsScalarDict HsDouble
  isIntegralDictInt : HsIsIntegralDict HsInt
  succHs : HsInt → HsInt
  zeroHs : HsInt
  trueHs falseHs : HsBool


toHsInt : ℕ → HsInt
toHsInt zero = zeroHs
toHsInt (suc n) = succHs (toHsInt n)

-- Haskell types
data Element : Set where
  Bool : Element
  Int : Element
  Float : Element
  Double : Element
  ZZ : Element
  ZC : Element → Element → Element
  Pair : Element → Element → Element
  FInt : ℕ → Element -- FInt n <=> [0..n-1]

-- and type classes
IsShape : Element → Shape → Set
IsShape ZZ Z = ⊤
IsShape (ZC e_sh Int) (sh :< n >) = IsShape e_sh sh
IsShape (ZC e_sh (FInt m)) (sh :< n >) = (m ≡ n) × (IsShape e_sh sh)
IsShape _ _ = ⊥

strongShapeToElement : (sh : Shape) → Σ Element (λ E → IsShape E sh)
strongShapeToElement Z = ZZ ,, _
strongShapeToElement (y :< y' >) with strongShapeToElement y 
... | ih = ZC (proj₁ ih) (FInt y') ,, (refl ,, proj₂ ih)

shapeToElement : (sh : Shape) → Σ Element (λ E → IsShape E sh)
shapeToElement Z = ZZ ,, _
shapeToElement (y :< y' >) with shapeToElement y 
... | ih = ZC (proj₁ ih) Int ,, proj₂ ih

IsNumeric : Element → Set
IsNumeric Int = ⊤
IsNumeric (FInt _) = ⊤
IsNumeric Float = ⊤
IsNumeric Double = ⊤
IsNumeric _ = ⊥

IsScalar : Element → Set
IsScalar Bool = ⊤
IsScalar Int = ⊤
IsScalar (FInt _) = ⊤
IsScalar Float = ⊤
IsScalar Double = ⊤
IsScalar _ = ⊥

IsIntegral : Element → Set
IsIntegral Int = ⊤
IsIntegral (FInt _) = ⊤
IsIntegral _ = ⊥

IsBits : Element → Set
IsBits Int = ⊤
IsBits (FInt _) = ⊤
IsBits _ = ⊥

EltType : Element → Set
EltType ZZ = HsZ
EltType (ZC e_sh e_n) = HsC (EltType e_sh) (EltType e_n)
EltType Bool = HsBool
EltType Int = HsInt
EltType Float = HsFloat
EltType Double = HsDouble
EltType (Pair a b) = HsPair (EltType a) (EltType b)
EltType (FInt _) = HsInt

ShapeDict : (sh : Shape) (E : Element) → IsShape E sh → HsShapeDict (EltType E)
ShapeDict sh Bool ()
ShapeDict sh Int ()
ShapeDict sh Float ()
ShapeDict sh Double ()
ShapeDict sh (Pair _ _) ()
ShapeDict sh (FInt _) ()
ShapeDict Z ZZ p = shapeDictZ
ShapeDict (y :< y' >) ZZ ()
ShapeDict Z (ZC y Int) ()
ShapeDict (y :< y' >) (ZC y0 Int) p = shapeDictC (ShapeDict y y0 p)
ShapeDict Z (ZC y (FInt _)) ()
ShapeDict (y :< m >) (ZC y0 (FInt n)) p = shapeDictC (ShapeDict y y0 (proj₂ p))
ShapeDict sh (ZC y Bool) ()
ShapeDict sh (ZC y Float) ()
ShapeDict sh (ZC y Double) ()
ShapeDict sh (ZC y ZZ) ()
ShapeDict sh (ZC y (ZC _ _)) ()
ShapeDict sh (ZC y (Pair _ _)) ()


SizedShapeDict : (sh : Shape) (E : Element) → IsShape E sh → HsSizedShapeDict (EltType E)
SizedShapeDict sh Bool ()
SizedShapeDict sh Int ()
SizedShapeDict sh Float ()
SizedShapeDict sh Double ()
SizedShapeDict sh (Pair _ _) ()
SizedShapeDict sh (FInt _) ()
SizedShapeDict Z ZZ p = sizedShapeDictZ
SizedShapeDict (y :< y' >) ZZ ()
SizedShapeDict Z (ZC y Int) ()
SizedShapeDict (y :< y' >) (ZC y0 Int) p = sizedShapeDictC (toHsInt y') (SizedShapeDict y y0 p)
SizedShapeDict Z (ZC y (FInt _)) ()
SizedShapeDict (y :< y' >) (ZC y0 (FInt _)) p = sizedShapeDictC (toHsInt y') (SizedShapeDict y y0 (proj₂ p))
SizedShapeDict sh (ZC y Bool) ()
SizedShapeDict sh (ZC y Float) ()
SizedShapeDict sh (ZC y Double) ()
SizedShapeDict sh (ZC y ZZ) ()
SizedShapeDict sh (ZC y (ZC _ _)) ()
SizedShapeDict sh (ZC y (Pair _ _)) ()


EltDict : (E : Element) → HsEltDict (EltType E)
EltDict ZZ = eltDictZZ
EltDict (ZC e_sh e_n) = eltDictZC (EltDict e_sh) (EltDict e_n)
EltDict Bool = eltDictBool
EltDict Int = eltDictInt
EltDict Float = eltDictFloat
EltDict Double = eltDictDouble
EltDict (Pair a b) = eltDictPair (EltDict a) (EltDict b)
EltDict (FInt _) = eltDictInt

IsNumDict : (E : Element) → {{p : IsNumeric E}} → HsIsNumDict (EltType E)
IsNumDict (ZC _ _) {{()}}
IsNumDict ZZ {{()}}
IsNumDict Bool {{()}}
IsNumDict (Pair _ _) {{()}}
IsNumDict Int = isNumDictInt
IsNumDict Float = isNumDictFloat
IsNumDict Double = isNumDictDouble
IsNumDict (FInt _) = isNumDictInt

ReadDict : (E : Element) → {{p : IsNumeric E}} → HsReadDict (EltType E)
ReadDict (ZC _ _) {{()}}
ReadDict ZZ {{()}}
ReadDict Bool = readDictBool
ReadDict Int = readDictInt
ReadDict (FInt _) = readDictInt
ReadDict Float = readDictFloat
ReadDict Double = readDictDouble
ReadDict (Pair _ _) {{()}}

IsScalarDict : (E : Element) → {{p : IsScalar E}} → HsIsScalarDict (EltType E)
IsScalarDict Bool {{p}} = isScalarDictBool
IsScalarDict Int {{p}} = isScalarDictInt
IsScalarDict (FInt _) {{p}} = isScalarDictInt
IsScalarDict Float {{p}} = isScalarDictFloat
IsScalarDict Double {{p}} = isScalarDictDouble
IsScalarDict ZZ {{()}}
IsScalarDict (ZC y y') {{()}}
IsScalarDict (Pair y y') {{()}}


IsIntegralDict : (E : Element) → {{p : IsIntegral E}} → HsIsIntegralDict (EltType E)
IsIntegralDict Bool {{()}}
IsIntegralDict Int {{p}} = isIntegralDictInt
IsIntegralDict (FInt _) {{p}} = isIntegralDictInt
IsIntegralDict Float {{()}}
IsIntegralDict Double {{()}}
IsIntegralDict ZZ {{()}}
IsIntegralDict (ZC y y') {{()}}
IsIntegralDict (Pair y y') {{()}}

BitsDict : (E : Element) → {{p : IsBits E}} → HsBitsDict (EltType E)
BitsDict Bool {{()}}
BitsDict Int {{p}} = bitsDictInt
BitsDict (FInt _) {{p}} = bitsDictInt
BitsDict Float {{()}}
BitsDict Double {{()}}
BitsDict ZZ {{()}}
BitsDict (ZC y y') {{()}}
BitsDict (Pair y y') {{()}}

data PreArray (Elt : Element) : Shape → Set where
  PA : {sh : Shape} → HsArray HsDIM1 (EltType Elt) → PreArray Elt sh

-- there could be another argument that links the HsDIM? with the actual shape
-- it's not clear, how to do this without having a different Ar constructor
-- for each shape rank
data Array (Elt : Element) : Shape → Set where
  Ar : {sh : Shape} → Acc (AccArray HsDIM1 (EltType Elt)) → Array Elt sh

unAr : {E : Element} {sh : Shape} → Array E sh → Acc (AccArray HsDIM1 (EltType E))
unAr {E}{sh} (Ar a) = a

data Exp (Elt : Element) : Set where
  Ex : AccExp (EltType Elt) → Exp Elt

{-# COMPILED_TYPE HsPair           (,) #-}
{-# COMPILED      fstHs            Prelude.fst #-}
{-# COMPILED      sndHs            Prelude.snd #-}
{-# COMPILED_TYPE HsZ              Data.Array.Accelerate.Z #-}
{-# COMPILED_TYPE HsC              Data.Array.Accelerate.:. #-}
{-# COMPILED_TYPE HsBool           Bool #-}
{-# COMPILED_TYPE HsInt            Int #-}
{-# COMPILED_TYPE HsFloat          Float #-}
{-# COMPILED_TYPE HsDouble         Double #-}
{-# COMPILED_TYPE HsArray          Accel.Array #-}
{-# COMPILED_TYPE HsEltDict        Accel.EltDict #-}
{-# COMPILED_TYPE HsShapeDict      Accel.ShapeDict #-}
{-# COMPILED_TYPE HsSizedShapeDict Accel.SizedShapeDict #-}
{-# COMPILED_TYPE HsIsNumDict      Accel.IsNumDict #-}
{-# COMPILED_TYPE HsReadDict       Accel.ReadDict #-}
{-# COMPILED_TYPE HsIsScalarDict   Accel.IsScalarDict #-}
{-# COMPILED_TYPE HsIsIntegralDict Accel.IsIntegralDict #-}
{-# COMPILED_TYPE HsBitsDict       Accel.BitsDict #-}
{-# COMPILED_TYPE AccArray         Data.Array.Accelerate.Array #-}
{-# COMPILED_TYPE Acc              Data.Array.Accelerate.Acc #-}
{-# COMPILED_TYPE AccExp           Data.Array.Accelerate.Exp #-}
{-# COMPILED_TYPE HsDIM0           Data.Array.Accelerate.DIM0 #-}
{-# COMPILED_TYPE HsDIM1           Data.Array.Accelerate.DIM1 #-}
{-# COMPILED_TYPE HsDIM2           Data.Array.Accelerate.DIM2 #-}
{-# COMPILED_TYPE HsDIM3           Data.Array.Accelerate.DIM3 #-}
{-# COMPILED eltDictZZ             Accel.eltDictZZ #-}
{-# COMPILED eltDictZC             (\_ _ -> Accel.eltDictZC) #-}
{-# COMPILED eltDictPair           (\_ _ -> Accel.eltDictPair) #-}
{-# COMPILED eltDictBool           Accel.eltDictBool #-}
{-# COMPILED eltDictInt            Accel.eltDictInt #-}
{-# COMPILED eltDictFloat          Accel.eltDictFloat #-}
{-# COMPILED eltDictDouble         Accel.eltDictDouble #-}
{-# COMPILED isNumDictInt          Accel.isNumDictInt #-}
{-# COMPILED isNumDictFloat        Accel.isNumDictFloat #-}
{-# COMPILED isNumDictDouble       Accel.isNumDictDouble #-}
{-# COMPILED readDictBool          Accel.readDictBool #-}
{-# COMPILED readDictInt           Accel.readDictInt #-}
{-# COMPILED readDictFloat         Accel.readDictFloat #-}
{-# COMPILED readDictDouble        Accel.readDictDouble #-}
{-# COMPILED bitsDictInt           Accel.bitsDictInt #-}
{-# COMPILED shapeDictZ            Accel.shapeDictZ #-}
{-# COMPILED shapeDictC            (\_ -> Accel.shapeDictC #-}
{-# COMPILED sizedShapeDictZ       Accel.sizedShapeDictZ #-}
{-# COMPILED sizedShapeDictC       (\_ -> Accel.sizedShapeDictC #-}
{-# COMPILED isScalarDictBool      Accel.isScalarDictBool #-}
{-# COMPILED isScalarDictInt       Accel.isScalarDictInt #-}
{-# COMPILED isScalarDictFloat     Accel.isScalarDictFloat #-}
{-# COMPILED isScalarDictDouble    Accel.isScalarDictDouble #-}
{-# COMPILED succHs                succ #-}
{-# COMPILED zeroHs                0 #-}
{-# COMPILED trueHs                True #-}
{-# COMPILED falseHs               False #-}

PreVector : ∀ (n : ℕ) → Element → Set
PreVector n A = PreArray A [ n ]

Vector : ∀ (n : ℕ) → Element → Set
Vector n A = Array A [ n ]

Scalar : Element → Set
Scalar A = Array A Z

postulate
  showArrayHs : {E : Set} → HsEltDict E → HsArray HsDIM1 E → String
  useHs : {E : Set} → HsEltDict E → HsArray HsDIM1 E → Acc (AccArray HsDIM1 E)
  runHs : {E : Set} → HsEltDict E → Acc (AccArray HsDIM1 E) → HsArray HsDIM1 E
  fromListHs : {E : Set} → HsEltDict E → List E → HsArray HsDIM1 E
  generateHs : {A IX : Set}
             → HsEltDict A
             → HsSizedShapeDict IX
             → (AccExp IX → AccExp A)
             → Acc (AccArray HsDIM1 A)
  foldHs : {A : Set}
          → HsEltDict A
          → HsInt
          → HsInt
          → (AccExp A → AccExp A → AccExp A)
          → AccExp A
          → Acc (AccArray HsDIM1 A)
          → Acc (AccArray HsDIM1 A)
  fold1Hs : {A : Set}
          → HsEltDict A
          → HsInt
          → HsInt
          → (AccExp A → AccExp A → AccExp A)
          → Acc (AccArray HsDIM1 A)
          → Acc (AccArray HsDIM1 A)
  -- scanl :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp a -> Acc (Vector a) -> Acc (Vector a)
  prescanrHs prescanlHs scanlHs : {A : Set}
          → HsEltDict A
          → (AccExp A → AccExp A → AccExp A)
          → AccExp A
          → Acc (AccArray HsDIM1 A)
          → Acc (AccArray HsDIM1 A)
  -- scanl' :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp a -> Acc (Vector a) -> (Acc (Vector a), Acc (Scalar a))
  scanl'Hs : {A : Set}
           → HsEltDict A
           → (AccExp A → AccExp A → AccExp A)
           → AccExp A
           → Acc (AccArray HsDIM1 A)
           → HsPair (Acc (AccArray HsDIM1 A)) (Acc (AccArray HsDIM1 A))
  -- scanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector a) -> Acc (Vector a)
  scanl1Hs : {A : Set}
           → HsEltDict A
           → (AccExp A → AccExp A → AccExp A)
           → Acc (AccArray HsDIM1 A)
           → Acc (AccArray HsDIM1 A)
  permuteHs : ∀ {A IXarg IXres}
            → HsEltDict A
            → HsSizedShapeDict IXarg
            → HsSizedShapeDict IXres
            → (AccExp A → AccExp A → AccExp A)
            → Acc (AccArray HsDIM1 A)
            → (AccExp IXarg → AccExp IXres)
            → Acc (AccArray HsDIM1 A)
            → Acc (AccArray HsDIM1 A)
  backpermuteHs : ∀ {A IXres IXarg}
                → HsEltDict A
                → HsSizedShapeDict IXarg
                → HsShapeDict IXres
                → AccExp IXres
                → (AccExp IXres → AccExp IXarg)
                → Acc (AccArray HsDIM1 A)
                → Acc (AccArray HsDIM1 A)
  !Hs : ∀ {A IX}
      → HsEltDict A
      → HsSizedShapeDict IX
      → Acc (AccArray HsDIM1 A)
      → AccExp IX
      → AccExp A
  zipHs : ∀ {A B}
          → HsEltDict A
          → HsEltDict B
          → Acc (AccArray HsDIM1 A)
          → Acc (AccArray HsDIM1 B)
          → Acc (AccArray HsDIM1 (HsPair A B))
  zipWithHs : ∀ {A B C}
          → HsEltDict A
          → HsEltDict B
          → HsEltDict C
          → (AccExp A → AccExp B → AccExp C)
          → Acc (AccArray HsDIM1 A)
          → Acc (AccArray HsDIM1 B)
          → Acc (AccArray HsDIM1 C)
  mapHs : ∀ {A B}
        → HsEltDict A
        → HsEltDict B
        → (AccExp A → AccExp B)
        → Acc (AccArray HsDIM1 A)
        → Acc (AccArray HsDIM1 B)
  theHs : ∀ {E}
        → HsEltDict E
        → Acc (AccArray HsDIM1 E) 
        → AccExp E

  >->Hs : ∀ {A B C}
        → (Acc (AccArray HsDIM1 A) → Acc (AccArray HsDIM1 B))
        → (Acc (AccArray HsDIM1 B) → Acc (AccArray HsDIM1 C))
        → (Acc (AccArray HsDIM1 A) → Acc (AccArray HsDIM1 C))

  addHs subHs   : {E : Set} → HsEltDict E → HsIsNumDict E
          → AccExp E → AccExp E → AccExp E 
  ε-addHs : {E : Set} → HsEltDict E → HsIsNumDict E → AccExp E
  mulHs   : {E : Set} → HsEltDict E → HsIsNumDict E
          → AccExp E → AccExp E → AccExp E
  absHs   : {E : Set} → HsEltDict E → HsIsNumDict E
          → AccExp E → AccExp E
  xorHs : {E : Set} → HsEltDict E → HsIsIntegralDict E
        → AccExp E → AccExp E → AccExp E
  shiftRHs : {E : Set} → HsEltDict E → HsIsIntegralDict E
        → AccExp E → AccExp HsInt → AccExp E
  bitAndHs : {E : Set} → HsEltDict E → HsBitsDict E
        → AccExp E → AccExp E → AccExp E
  boolToIntHs : AccExp HsBool → AccExp HsInt
  notHs : AccExp HsBool → AccExp HsBool
  &&Hs ||Hs : AccExp HsBool → AccExp HsBool → AccExp HsBool
  iteHs : {E : Set} → HsEltDict E
        → AccExp HsBool → AccExp E → AccExp E → AccExp E
  eqlHs : {E : Set} → HsEltDict E → HsIsScalarDict E 
        → AccExp E → AccExp E → AccExp HsBool
  constantHs : {E : Set} → HsEltDict E
             → E → AccExp E
  fstExp : ∀ {A B} → HsEltDict A → HsEltDict B → AccExp (HsPair A B) → AccExp A
  sndExp : ∀ {A B} → HsEltDict A → HsEltDict B → AccExp (HsPair A B) → AccExp B
  pairExp : ∀ {A B} → HsEltDict A → HsEltDict B → AccExp A → AccExp B → AccExp (HsPair A B)

  index0Hs : AccExp HsZ
  index1Hs : AccExp HsInt → AccExp (HsC HsZ HsInt)
  unindex1Hs : AccExp (HsC HsZ HsInt) → AccExp HsInt

  constantFloat : String → AccExp HsFloat
  constantDouble : String → AccExp HsDouble
  constantInt : String → AccExp HsInt
  constantFromString : {E : Set} → HsEltDict E → HsReadDict E → String → AccExp E
  valFromString : {E : Set} → HsReadDict E → String → E

{-# COMPILED useHs       (\ _ -> Accel.use) #-}
{-# COMPILED runHs       (\ _ -> Accel.run) #-}
{-# COMPILED fromListHs  (\_ -> Accel.fromList) #-}
{-# COMPILED generateHs  (\_ -> Accel.generate) #-}
{-# COMPILED foldHs      (\_ -> Accel.fold) #-}
{-# COMPILED fold1Hs     (\_ -> Accel.fold1) #-}
{-# COMPILED scanlHs     (\_ -> Accel.scanl) #-}
{-# COMPILED prescanlHs  (\_ -> Accel.prescanl) #-}
{-# COMPILED prescanrHs  (\_ -> Accel.prescanr) #-}
{-# COMPILED scanl'Hs    (\_ -> Accel.scanl') #-}
{-# COMPILED scanl1Hs    (\_ -> Accel.scanl1) #-}
{-# COMPILED backpermuteHs (\_ _ _ -> Accel.backpermute) #-}
{-# COMPILED permuteHs   (\_ _ _ -> Accel.permute) #-}
{-# COMPILED zipWithHs   (\_ _ _ -> Accel.zipWith) #-}
{-# COMPILED !Hs         (\_ _ -> (Accel.!)) #-}
{-# COMPILED zipHs       (\_ _ -> Accel.zip) #-}
{-# COMPILED mapHs       (\ _ _ -> Accel.map) #-}
{-# COMPILED theHs       (\ _ -> Accel.the) #-}
{-# COMPILED >->Hs       (\ _ _ _ -> (Accel.>->)) #-}

{-# COMPILED addHs       (\ _ -> Accel.mkAdd) #-}
{-# COMPILED subHs       (\ _ -> Accel.mkSub) #-}
{-# COMPILED xorHs       (\ _ -> Accel.mkBXor) #-}
{-# COMPILED shiftRHs    (\ _ -> Accel.mkShiftR) #-}
{-# COMPILED bitAndHs    (\ _ -> Accel.mkBitAnd) #-}
{-# COMPILED ε-addHs     (\ _ ed nd -> Accel.constant ed nd 0) #-}
{-# COMPILED mulHs       (\ _ -> Accel.mkMul) #-}
{-# COMPILED absHs       (\ _ -> Accel.mkAbs) #-}
{-# COMPILED boolToIntHs Data.Array.Accelerate.boolToInt #-}
{-# COMPILED notHs       Data.Array.Accelerate.not #-}
{-# COMPILED &&Hs        (Data.Array.Accelerate.&&*) #-}
{-# COMPILED ||Hs        (Data.Array.Accelerate.||*) #-}
{-# COMPILED iteHs       (\ _ -> Accel.mkIte) #-}
{-# COMPILED fstExp      (\ _ _ -> Accel.fst) #-}
{-# COMPILED sndExp      (\ _ _ -> Accel.snd) #-}
{-# COMPILED pairExp     (\ _ _ -> Accel.pair) #-}
{-# COMPILED constantHs  (\ _ -> Accel.constant) #-}
{-# COMPILED eqlHs       (\ _ -> Accel.mkEql) #-}

{-# COMPILED index0Hs    Data.Array.Accelerate.index0 #-}
{-# COMPILED index1Hs    Data.Array.Accelerate.index1 #-}
{-# COMPILED unindex1Hs  Data.Array.Accelerate.unindex1 #-}

{-# COMPILED showArrayHs (\ _ -> Accel.showArray) #-}
{-# COMPILED constantInt Accel.constantInt #-}
{-# COMPILED constantFloat Accel.constantFloat #-}
{-# COMPILED constantDouble Accel.constantDouble #-}
{-# COMPILED constantFromString (\ _ -> Accel.constantFromString) #-}
{-# COMPILED valFromString (\ _ -> Accel.valFromString) #-}

-- does not (necessarily) print the correct shape
-- because it always yields a 1-d array
-- but the elements are printed correctly
showArray : {E : Element} {sh : Shape} → PreArray E sh → String
showArray {E} (PA y) = showArrayHs (EltDict E) y

wrap_a : ∀ {A B sha shb}
       → (Acc (AccArray HsDIM1 (EltType A)) → Acc (AccArray HsDIM1 (EltType B)))
       → (Array A sha → Array B shb)
wrap_a f (Ar a) = Ar (f a)

unwrap_a : ∀ {A B sha shb}
       → (Array A sha → Array B shb)
       → (Acc (AccArray HsDIM1 (EltType A)) → Acc (AccArray HsDIM1 (EltType B)))
unwrap_a {A}{B}{sha}{shb} f = λ a → unAr (f (Ar a))

unwrap2 : {A B C : Element}
       → (Exp A → Exp B → Exp C)
       → (AccExp (EltType A) → AccExp (EltType B) → AccExp (EltType C))
unwrap2 f x y with f (Ex x) (Ex y)
... | Ex fxy = fxy

unwrap1 : {A B : Element}
       → (Exp A → Exp B)
       → (AccExp (EltType A) → AccExp (EltType B))
unwrap1 f x with f (Ex x)
... | Ex fx = fx

wrap3 : {A B C D : Element}
     → (AccExp (EltType A) → AccExp (EltType B) → AccExp (EltType C) → AccExp (EltType D))
     → (Exp A → Exp B → Exp C → Exp D)
wrap3 f (Ex x) (Ex y) (Ex z) = Ex (f x y z)

wrap2 : {A B C : Element}
     → (AccExp (EltType A) → AccExp (EltType B) → AccExp (EltType C))
     → (Exp A → Exp B → Exp C)
wrap2 f (Ex x) (Ex y) = Ex (f x y)

wrap1 : {A B : Element}
      → (AccExp (EltType A) → AccExp (EltType B)) 
      → (Exp A → Exp B)
wrap1 f (Ex x) = Ex (f x)

-- embedding of constants
{-
data Constant : Set where
  II : Constant
  FF : Constant
  DD : Constant

ConstantType : Constant → Element
ConstantType II = Int
ConstantType FF = Float
ConstantType DD = Double

C : (c : Constant) → String → Exp (ConstantType c)
C c s = Ex (constantFromString (EltDict (ConstantType c))
                               (ReadDict (ConstantType c))
                               s)
-}

-- you could write constants like this
-- ("3.1415926" ::: Float)
-- ("6.0221415E23" ::: Double)
_parsesAs_ : String → Element → AgBool
"" parsesAs E = false
"0" parsesAs E = true
s parsesAs Bool = isBoolLiteral s
s parsesAs Int = isIntLiteral s
s parsesAs Float = isFloatLiteral s
s parsesAs Double = isFloatLiteral s
s parsesAs _ = false

_:::_ : (s : String) → (E : Element) → {{nu : IsNumeric E}} → {p : T (s parsesAs E)} → Exp E
s ::: E = Ex (constantFromString (EltDict E) (ReadDict E) s)

-- ok:pa44 = "44" ::: Int
-- yellow:paxx = "xx" ::: Int

data TypedString : Element → Set where
  _:as:_ : (s : String) (E : Element) → TypedString E

parseable : {E : Element} → TypedString E → AgBool
parseable (s :as: E) = s parsesAs E

typedLiteral : {E : Element} {{nu : IsNumeric E}}
             → (ts : TypedString E)
             → T (parseable ts)
             → Exp E
typedLiteral (s :as: E) tpae = Ex (constantFromString (EltDict E) (ReadDict E) s)

-- ok:tl44 = typedLiteral ("44" :as: Int) tt
-- err:tlxx = typedLiteral ("xx" :as: Int) tt

⟪ : (E : Element) → {{nu : IsNumeric E}} → (s : String) → (p : T (s parsesAs E)) → Exp E
⟪ E s p = Ex (constantFromString (EltDict E) (ReadDict E) s)
⟫ = tt

-- ok:bb42 = ⟪ Int "42" ⟫
-- err:bbxx = ⟪ Int "xx" ⟫

{-
record ParsedAs (E : Element) : Set where
  field
    s : String
    parsedAs : T (s parsesAs E)

<< : (E : Element) → (s : String) → (p : T (s parsesAs E)) → ParsedAs E
<< E s p = record { s = s ; parsedAs = p }
>> = tt

ok:cc42 = << Int "42" >>
err:ccxx = << Int "xx" >>
-}

{- does not allow me to pattern match: s parsesAs E' != true
⟨_⟩ : ∀ {E} → ParsedString E true → Exp E
⟨ s :as: E ⟩ = {!!}
-}

_asVecOf'_ : {n : ℕ} → Vec String n → (E : Element) → {{nu : IsNumeric E}} → Vec (EltType E) n
v asVecOf' E = vmap (λ s → valFromString (ReadDict E) s) v

_asArrayOf_ : {n : ℕ} → Vec String n → (E : Element) → {{nu : IsNumeric E}} → PreArray E [ n ]
v asArrayOf E = PA (fromListHs (EltDict E) (Data.Vec.toList (v asVecOf' E)))

_asArrOf_,_,_ : {n : ℕ}
           → Vec String n
           → (E : Element) → {{nu : IsNumeric E}}
           → (sh : Shape)
           → (p : n ≡ size sh)
           → PreArray E sh
v asArrOf E , sh , p =
  PA (fromListHs (EltDict E) (Data.Vec.toList (v asVecOf' E)))

-- * the user visible interface
use  : {sh : Shape}{E : Element} → PreArray E sh → Array E sh
use {sh}{E} (PA y) = Ar (useHs (EltDict E) y)

-- the Haskell version is much more clever than this...
-- it can return any instance of the Arrays class
run : {sh : Shape} {E : Element} → Array E sh → PreArray E sh
run {sh}{E}(Ar y) = PA (runHs (EltDict E) y)

--
reshape : ∀ {oldshape : Shape}
         → {E : Element}
         → (newshape : Shape)
         → Array E oldshape
         → (size oldshape ≡ size newshape)
         → Array E newshape
reshape nsh (Ar y) p = Ar y

--
generate : ∀ {E}
         → (sh : Shape)
         → (Exp (proj₁ (shapeToElement sh)) → Exp E)
         → Array E sh
generate {E} sh f =
  let arginfo = shapeToElement sh
      IX   = proj₁ arginfo
      p    = proj₂ arginfo
  in
  Ar (generateHs (EltDict E) (SizedShapeDict sh IX p) (unwrap1 f))

--
strongGenerate : {E : Element}
               → (sh : Shape)
               → (Exp (proj₁ (strongShapeToElement sh)) → Exp E)
               → Array E sh
strongGenerate {E} sh f with strongShapeToElement sh
... | arginfo with proj₁ arginfo | proj₂ arginfo
... | IX | p  = 
  Ar (generateHs (EltDict E) (SizedShapeDict sh IX p) (unwrap1 f))

--
fold : ∀ {E}{sh}{n}
     → (Exp E → Exp E → Exp E)
     → Exp E
     → Array E (sh :< n >)
     → Array E sh
fold {E}{sh}{n} f (Ex e) (Ar a) =
  Ar (foldHs (EltDict E) (toHsInt (size sh)) (toHsInt n)
             (unwrap2 f) e a)

--
fold1 : ∀ {E}{sh}{n}
      → (Exp E → Exp E → Exp E)
      → Array E (sh :< n >)
      → (p : size sh *ℕ n > 0)
      → Array E sh
fold1 {E}{sh}{n} f (Ar a) p =
  Ar (fold1Hs (EltDict E) (toHsInt (size sh)) (toHsInt n)
             (unwrap2 f) a)

--
prescanr : ∀ {E n}
      → (Exp E → Exp E → Exp E)
      → Exp E
      → Vector n E
      → Vector n E
prescanr {E}{n} f (Ex e) (Ar a) =
  Ar (prescanrHs (EltDict E) (unwrap2 f) e a)

--
prescanl : ∀ {E n}
      → (Exp E → Exp E → Exp E)
      → Exp E
      → Vector n E
      → Vector n E
prescanl {E}{n} f (Ex e) (Ar a) =
  Ar (prescanlHs (EltDict E) (unwrap2 f) e a)

--
scanl : ∀ {E n}
      → (Exp E → Exp E → Exp E)
      → Exp E
      → Vector n E
      → Vector (suc n) E
scanl {E}{n} f (Ex e) (Ar a) =
  Ar (scanlHs (EltDict E) (unwrap2 f) e a)

--
scanl' : ∀ {E n}
       → (Exp E → Exp E → Exp E)
       → Exp E
       → Vector n E
       → (Vector n E × Scalar E)
scanl' {E}{n} f (Ex e) (Ar a) =
  let hspair = scanl'Hs (EltDict E) (unwrap2 f) e a
  in  Ar (fstHs hspair) ,, Ar (sndHs hspair)

--
scanl1 : ∀ {E n}
       → (Exp E → Exp E → Exp E)
       → Vector (suc n) E
       → Vector (suc (suc n)) E
scanl1 {E}{n} f (Ar a) =
  Ar (scanl1Hs (EltDict E) (unwrap2 f) a)

--
permute : ∀ {A IXres sh_res sh_arg}
            {pres : IsShape IXres sh_res}
        → (Exp A → Exp A → Exp A)
        → Array A sh_res
        → (Exp (proj₁ (shapeToElement sh_arg)) → Exp IXres)
        → Array A sh_arg
        → Array A sh_res
permute {A}{IXres}{sh_res}{sh_arg} {pres} f (Ar def) tr (Ar a) =
  let arginfo = shapeToElement sh_arg
      IXarg   = proj₁ arginfo
      parg    = proj₂ arginfo
  in
  Ar (permuteHs (EltDict A)
                (SizedShapeDict sh_arg IXarg parg)
                (SizedShapeDict sh_res IXres pres)
                (unwrap2 f)
                def (unwrap1 tr) a)

--
backpermute : ∀ {A IXres sh_res IXarg sh_arg}
                {pres : IsShape IXres sh_res}
                {parg : IsShape IXarg sh_arg}
            -- shape of the result
            → Exp IXres
            -- for each index in the result, tell me where it comes from
            → (Exp IXres → Exp IXarg)
            → Array A sh_arg
            → Array A sh_res
backpermute {A}{IXres}{sh_res}{IXarg}{sh_arg} {pres}{parg} (Ex ixres) f (Ar a) =
  Ar (backpermuteHs (EltDict A)
                    (SizedShapeDict sh_arg IXarg parg)
                    (ShapeDict sh_res IXres pres)
                    ixres (unwrap1 f) a)

--
zip : ∀ {A B} {sh}
        → Array A sh
        → Array B sh
        → Array (Pair A B) sh
zip{A}{B} (Ar as) (Ar bs) =
  Ar (zipHs (EltDict A) (EltDict B) as bs)

--
zipWith : ∀ {A B C} {sh}
        → (Exp A → Exp B → Exp C)
        → Array A sh
        → Array B sh
        → Array C sh
zipWith{A}{B}{C} f (Ar as) (Ar bs) =
  Ar (zipWithHs (EltDict A) (EltDict B) (EltDict C) (unwrap2 f) as bs)

--
map : ∀ {A B} {sh}
    → (Exp A → Exp B)
    → Array A sh
    → Array B sh
map{A}{B} f (Ar as) =
  Ar (mapHs (EltDict A) (EltDict B) (unwrap1 f) as)

--
_!_ : ∀ {A IX} {sh} {p : IsShape IX sh}
    → Array A sh
    → Exp IX
    → Exp A
_!_ {A}{IX}{sh}{p} (Ar a) (Ex ix) =
  Ex (!Hs (EltDict A) (SizedShapeDict sh IX p) a ix)

--
the : ∀ {E} → Scalar E → Exp E
the{E} (Ar y) = Ex (theHs (EltDict E) y)

--
_>->_ : ∀ {A B C sha shb shc}
      → (Array A sha → Array B shb)
      → (Array B shb → Array C shc)
      → (Array A sha → Array C shc)
_>->_ f g = wrap_a (>->Hs (unwrap_a f) (unwrap_a g))

-- * operations on abstract syntax
_+_ : {E : Element} {{p : IsNumeric E}} → Exp E → Exp E → Exp E
_+_ {E} = wrap2 (addHs (EltDict E) (IsNumDict E))

_-_ : {E : Element} {{p : IsNumeric E}} → Exp E → Exp E → Exp E
_-_ {E} = wrap2 (addHs (EltDict E) (IsNumDict E))

ε-+ : {E : Element} → {{nu : IsNumeric E}} → Exp E
ε-+ {E} = "0" ::: E

ε-add : {E : Element} {{p : IsNumeric E}} → Exp E
ε-add{E} = Ex (ε-addHs (EltDict E) (IsNumDict E))

_*_ : {E : Element} {{p : IsNumeric E}} → Exp E → Exp E → Exp E
_*_ {E} = wrap2 (mulHs (EltDict E) (IsNumDict E))

abs : {E : Element} {{p : IsNumeric E}} → Exp E → Exp E
abs {E} = wrap1 (absHs (EltDict E) (IsNumDict E))

_==_ : {E : Element} {{p : IsScalar E}} → Exp E → Exp E → Exp Bool
_==_ {E} = wrap2 (eqlHs (EltDict E) (IsScalarDict E))

_xor_ : {E : Element} {{p : IsIntegral E}} → Exp E → Exp E → Exp E
_xor_ {E} = wrap2 (xorHs (EltDict E) (IsIntegralDict E))

_&_ : {E : Element} {{p : IsBits E}} → Exp E → Exp E → Exp E
_&_ {E} = wrap2 (bitAndHs (EltDict E) (BitsDict E))

_shiftR_ : {E : Element} {{p : IsIntegral E}} → Exp E → Exp Int → Exp E
_shiftR_ {E} = wrap2 (shiftRHs (EltDict E) (IsIntegralDict E))

boolToInt : Exp Bool → Exp Int
boolToInt = wrap1 boolToIntHs

not : Exp Bool → Exp Bool
not = wrap1 notHs

_&&_ : Exp Bool → Exp Bool → Exp Bool
_&&_ = wrap2 &&Hs

_||_ : Exp Bool → Exp Bool → Exp Bool
_||_ = wrap2 ||Hs

if_then_else_ : {E : Element} → Exp Bool → Exp E → Exp E → Exp E
if_then_else_ {E} = wrap3 (iteHs (EltDict E))

fst : {E F : Element} → Exp (Pair E F) → Exp E
fst {E}{F} = wrap1 (fstExp (EltDict E) (EltDict F))

snd : {E F : Element} → Exp (Pair E F) → Exp F
snd {E}{F} = wrap1 (sndExp (EltDict E) (EltDict F))

pair : {E F : Element} → Exp E → Exp F → Exp (Pair E F)
pair {E}{F} = wrap2 (pairExp (EltDict E) (EltDict F))

constant : {E : Element} → EltType E → Exp E
constant {E} x = Ex (constantHs (EltDict E) x)

-- * index construction and destruction
index0 : Exp ZZ
index0 = Ex (index0Hs)

index1 : Exp Int → Exp (ZC ZZ Int)
index1 = wrap1 index1Hs

unindex1 : Exp (ZC ZZ Int) → Exp Int
unindex1 = wrap1 unindex1Hs

unindex1F : {n : ℕ} → Exp (ZC ZZ (FInt n)) → Exp (FInt n)
unindex1F = wrap1 unindex1Hs
