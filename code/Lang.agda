module Lang where

open import Algebra 
open import Algebra.Structures
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Fin hiding (_<_; _≤_; pred; _+_)
open import Data.List hiding (replicate; [_])
open import Data.List.All
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
open PropEq.≡-Reasoning

data Shape : List ℕ → Set where
  Z    : Shape []
  _::_ : ∀ {xs} → (n : ℕ) → Shape xs → Shape (n ∷ xs)

-- drawbacks:
-- * sequence reversed wrt Haskell : not a good idea because programmers except row column order
-- * how to generalize to slices?
{-
data Entry : Set where
  <_> : ℕ → Entry
  All : Entry
  Any : Entry

data Slice : List Entry → Set where
  Z : Slice []
  _::_ : ∀ {es} → (e : Entry) → Slice es → Slice (e ∷ es)

data IsShape : {es : List Entry} → Slice es → Set where
  IsZ : IsShape Z
  IsNum : ∀ {n es} → {sl : Slice es} → IsShape sl → IsShape (< n > :: sl)

data IsShape' : {es : List Entry} → Slice es → List ℕ → Set where
  IsZ' : IsShape' Z []
  IsNum' : ∀ {n ns es} → {sl : Slice es} → IsShape' sl ns → IsShape' (< n > :: sl) (n ∷ ns)

data Shape' : List ℕ → Set where
  Sh : {es : List Entry} → {ns : List ℕ} → (sl : Slice es) → IsShape' sl ns → Shape' ns
-}
{-
indexArray :: Array sh e → sh → e
arrayShape :: Array sh e → sh
arrayRank :: sh → Nat
arraySize :: sh → Nat
-}
{-
arrayRank : ∀ {xs} → Shape xs → ℕ
arrayRank {xs} _ = length xs

arraySize : ∀ {xs} → Shape xs → ℕ
arraySize {xs} _ = product xs

FillSlice : List Entry → List ℕ → List ℕ
FillSlice [] ns = []
FillSlice (< y > ∷ xs) ns = y ∷ FillSlice xs ns
FillSlice (All ∷ xs) [] = {!!}
FillSlice (All ∷ xs) (x ∷ xs') = x ∷ FillSlice xs xs'
FillSlice (Any ∷ xs) ns = {!!}

postulate Array : Set → Set → Set
-}

-- questions
-- * what about dependent arrays where the type depends on the index
-- value? It's a logical consequence of dependent function types...
-- * generate: the Fin in NIndex could be bloody inconvenient because the function
-- has to work with Fin stuff which requires conversion and
-- potentially bounds proofs. It may not be needed in this case
-- because it unnecessarily restricts the function to a smaller domain
-- * reshape : equality proof as implicit or explicit argument?
-- Position in argument list?
-- * relation between slice and replicate? Does it hold that 
--   arr == slice (replicate slix arr) slix 
-- * slice : statically check that the slice indexes are in their bounds?
-- * zipWith : should all arguments be restricted to the same shape or
-- is it intended to compute the intersection shape? There could be
-- two alternative typings.
-- * Segments:  this is a vector of segment lengths?

-- another try
-- the slice type registers the number of All and Any operators
-- shape is a special slice


data NSlice : ℕ → Bool → Set where
  Z     : NSlice 0 false
  Any   : NSlice 0 true
  _:<_> : ∀ {m n} → NSlice m n → ℕ → NSlice m n
  _:All : ∀ {m n} → NSlice m n → NSlice (suc m) n

-- "nicer" syntax?
_[_] : ∀ {m n} → NSlice m n → ℕ → NSlice m n
_[_]{m}{n} = _:<_>{m}{n}

[_] = _[_] Z

_[All] : ∀ {m n} → NSlice m n → NSlice (suc m) n
_[All]{m}{n} = _:All{m}{n}

NShape = NSlice 0 false

postulate NArray : NShape → Set → Set
postulate arrayToList : ∀ {shape}{A} → NArray shape A → List A

NVector : ∀ (n : ℕ) → Set → Set
NVector n A = NArray (Z :< n >) A

NScalar : Set → Set
NScalar A = NArray Z A

nsRank : NShape → ℕ
nsRank Z = 0
nsRank (y :< y' >) = suc (nsRank y)

nsSize : NShape → ℕ
nsSize Z = 1
nsSize (y :< y' >) = y' * nsSize y

rankCheck : Bool → ℕ → ℕ → Set
rankCheck b rank m = if b then  rank ≥ m else rank ≡ m

-- takes a slice with :All and a shape
-- returns the slice "filled in" with the shape
NFillSlice : ∀ {m : ℕ} → {b : Bool}
           → NSlice m b → (fill : NShape)
           → rankCheck b (nsRank fill) m
           → NShape
NFillSlice Z Z p = Z
NFillSlice {.0} {false} Z (y :< y' >) ()
NFillSlice {b = true} Any fi p = fi
NFillSlice (y :< y' >) fi p = NFillSlice y fi p :< y' >
NFillSlice {.(suc _)} {true} (y :All) Z ()
NFillSlice {.(suc _)} {false} (y :All) Z ()
NFillSlice {.(suc _)} {true} (y :All) (y' :< y0 >) (s≤s m≤n) = NFillSlice y y' m≤n :< y0 >
NFillSlice {.(suc (nsRank y'))} {false} (y :All) (y' :< y0 >) refl = NFillSlice y y' refl :< y0 >

-- replicate :: (Slice slix, Elt e)
--           => Exp slix
--           -> Acc (Array (SliceShape slix) e)
--           -> Acc (Array (FullShape slix) e)

postulate
 nreplicate  : ∀ {m b}
               → {shape : NShape}
               → {p : rankCheck b (nsRank shape) m}
               → {e : Set}
            → (slice : NSlice m b)
            → NArray shape e
            → NArray (NFillSlice slice shape p) e


-- generate :: (Shape ix, Elt a)
--          => Exp ix
--          -> (Exp ix -> Exp a)
--          -> Acc (Array ix a)

data NIndex : NShape → Set where
  Z  : NIndex Z
  _:<_> : ∀ {sh} → {n : ℕ} → NIndex sh → Fin n → NIndex (sh :< n >)

postulate
 ngenerate : ∀ {e} 
          → (shape : NShape)
          → (NIndex shape → e)
          → NArray shape e

postulate 
  _!_ : ∀ {e}{shape}
    → NArray shape e
    → NIndex shape
    → e

-- > precondition: size ix == size ix'
--
-- reshape :: (Shape ix, Shape ix', Elt e) 
--         => Exp ix 
--         -> Acc (Array ix' e) 
--         -> Acc (Array ix e)

postulate
 nreshape : ∀ {oldshape : NShape}
         → {e : Set}
         → (newshape : NShape)
         → NArray oldshape e
         → (nsSize oldshape ≡ nsSize newshape)
         → NArray newshape e


-- slice :: (Slice slix, Elt e) 
--      => Acc (Array (FullShape slix) e) 
--      -> Exp slix 
--      -> Acc (Array (SliceShape slix) e)
-- *** need to permute arguments because of dependency
-- *** does not have enough information to prevent rt errors: consider this
-- slice (Z :< x0 > :All :All) (a : A (Z :< x > :< y > :< z >)) 
--    -> A (Z :< y > :< z >)
-- but x0 < x should also be enforced 

-- isGIndex : (slice : NSlice m b) → (shape : NShape)
--          → {p : rankCheck b (nsRank shape) m}
--          → Set
data IsGIndex : {m : ℕ} {b : Bool} (slice : NSlice m b) (shape : NShape) → Set where
  isG-Z     : IsGIndex Z Z
  isG-Index : ∀ {m} {b} {sl} {n0} {sh} {n}
            → n0 ≤ n
            → IsGIndex{m}{b} sl sh → IsGIndex{m}{b} (sl :< n0 >) (sh :< n >)
  isG-All   : ∀ {m} {b} {sl} {sh} {n}
            → IsGIndex{m}{b} sl sh → IsGIndex{suc m}{b} (sl :All) (sh :< n >)
  isG-Any   : ∀ {sh}
            → IsGIndex Any sh

postulate
 nslice : ∀ {m b} →
            {shape : NShape} →
            {p : rankCheck b (nsRank shape) m} →
            {e : Set}
       → (slice : NSlice m b)
       → IsGIndex slice shape
       → NArray (NFillSlice slice shape p) e
       → NArray shape e

postulate
 nmap : ∀ {A B : Set} {shape : NShape}
     → (A → B)
     → NArray shape A
     → NArray shape B


postulate
 nzipWith : ∀ {A B C : Set} {shape : NShape}
         → (A → B → C)
         → NArray shape A
         → NArray shape B
         → NArray shape C

-- if you don't get this rank business to work, then it might be
-- necessary to define a rank comparison directly on shapes
nsr-comp : ∀ {n1 n2 : ℕ} (sh1 sh2 : NShape)
         → nsRank sh1 ≡ nsRank sh2
         → nsRank (sh1 :< n1 >) ≡ nsRank (sh2 :< n2 >)
nsr-comp {n1}{n2} sh1 sh2 p = 
  begin
    nsRank (sh1 :< n1 >)
  ≡⟨ cong suc p ⟩
    nsRank (sh2 :< n2 >)
  ∎

nsr-pmoc : ∀ (n1 n2 : ℕ) (sh1 sh2 : NShape)
         → nsRank (sh1 :< n1 >) ≡ nsRank (sh2 :< n2 >)
         → nsRank sh1 ≡ nsRank sh2
nsr-pmoc n1 n2 sh1 sh2 p = 
  begin
    nsRank (sh1 )
  ≡⟨ refl ⟩
    pred (nsRank (sh1 :< n1 >))
  ≡⟨ cong pred p ⟩
    pred (nsRank (sh2 :< n2 >))
  ≡⟨ refl ⟩
    nsRank (sh2 )
  ∎

Intersect : (sh1 sh2 : NShape) (p : nsRank sh1 ≡ nsRank sh2) →  NShape
Intersect Z Z p = Z
Intersect Z (y :< y' >) ()
Intersect (y :< y' >) Z ()
Intersect (y :< y' >) (y0 :< y1 >) p = 
  Intersect y y0 (nsr-pmoc y' y1 y y0 p) :< y' ⊔ y1 >

postulate
 nzipWith' : ∀ {A B C : Set}
              {shapeA shapeB : NShape}
              {p : nsRank shapeA ≡ nsRank shapeB}
         → (A → B → C)
         → NArray shapeA A
         → NArray shapeB B
         → NArray (Intersect shapeA shapeB p) C

-- fold :: (Shape ix, Elt a)
--     => (Exp a -> Exp a -> Exp a) 
--     -> Exp a 
--     -> Acc (Array (ix:.Int) a)
--     -> Acc (Array ix a)

-- might want to choose one or more dimensions for reduction
-- extreme case: reduce across all dimensions to a single value

postulate
  nfold : ∀ {A}{n}{shape}
          → (A → A → A)
          → A
          → NArray (shape :< n >) A
          → NArray shape A

-- we might want to plug in a monoid
nfold' : ∀ {n}{sh} (m : Monoid _ _)
       → let open Monoid m in NArray (sh :< n >) Carrier
       → NArray sh Carrier
nfold'{n}{sh} m ar =
  let open Monoid m in
  nfold{Carrier}{n}{sh} _∙_ ε ar

-- this refers to Data.Nat.Properties
open IsCommutativeSemiring isCommutativeSemiring
open IsCommutativeMonoid +-isCommutativeMonoid
open IsCommutativeMonoid *-isCommutativeMonoid
  using () renaming (identityˡ to identity-2)

ℕ-+-monoid : Monoid _ _
ℕ-+-monoid = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _∙_ = _+_
  ; ε = 0
  ; isMonoid = 
    record
    { isSemigroup = isSemigroup
    ; identity = identityˡ , identity-2
    }
  }

ℕ-+-semigroup : Semigroup _ _
ℕ-+-semigroup = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _∙_ = _+_
  ; isSemigroup = isSemigroup
  }


-- fold1 :: (Shape ix, Elt a)
--      => (Exp a -> Exp a -> Exp a) 
--      -> Acc (Array (ix:.Int) a)
--      -> Acc (Array ix a)

postulate 
  nfold1 : ∀ {A}{n}{shape}{p : n * nsSize shape > 0}
         → (A → A → A)
         → NArray (shape :< n >) A
         → NArray shape A

-- plug in a semigroup
nfold1' : ∀ {n}{sh}{p : n * nsSize sh > 0}
        → (m : Semigroup _ _)
        → let open Semigroup m in
          NArray (sh :< n >) Carrier
        → NArray sh Carrier
nfold1'{n}{sh}{p} m ar = let open Semigroup m in
  nfold1{Carrier}{n}{sh}{p} _∙_ ar

-- foldSeg :: (Shape ix, Elt a)
--        => (Exp a -> Exp a -> Exp a) 
--         -> Exp a 
--         -> Acc (Array (ix:.Int) a)
--         -> Acc Segments
--         -> Acc (Array (ix:.Int) a)

-- type Segments = Vector Int
-- type Vector e = Array DIM1 e

sumA : ∀ {n}{shape} → NArray (shape :< n >) ℕ → NArray shape ℕ
sumA = nfold _+_ 0

postulate scalar : ∀ {A} → NArray Z A → A

-- Segments m n : vector of m numbers adding up to n
record Segments (m n : ℕ) : Set where
  field
    vec   : NArray (Z :< m >) ℕ
    addup : scalar (sumA vec) ≡ n

postulate
  nfoldSeg : ∀ {A}{m n}{shape}
           → (A → A → A)
           → A
           → NArray (shape :< n >) A
           → Segments m n
           → NArray (shape :< m >) A

-- fold1Seg :: (Shape ix, Elt a)
--          => (Exp a -> Exp a -> Exp a) 
--          -> Acc (Array (ix:.Int) a)
--          -> Acc Segments
--          -> Acc (Array (ix:.Int) a)

-- Segments1 m n : vector of m numbers > 0 adding up to n
record Segments1 (m n : ℕ) : Set where
  field
    -- segs  : Segments m n
    -- could not refer to segs.vec
    vec   : NArray (Z :< m >) ℕ
    addup : scalar (sumA vec) ≡ n
    all>0 : All (λ i → i > 0)  (arrayToList vec)

postulate
  nfold1Seg : ∀ {A}{m n}{shape}{p : n * nsSize shape > 0}
           → (A → A → A)
           → NArray (shape :< n >) A
           → Segments1 m n
           → NArray (shape :< m >) A

-- scanl :: Elt a
--      => (Exp a -> Exp a -> Exp a)  -- should be associative
--      -> Exp a
--      -> Acc (Vector a)
--      -> Acc (Vector a)

postulate 
  nscanl : ∀ {A}{n}
         → (A → A → A)
         → A
         → NVector n A
         → NVector (suc n) A

-- scanl' :: Elt a
--        => (Exp a -> Exp a -> Exp a)
--        -> Exp a
--        -> Acc (Vector a)
--        -> (Acc (Vector a), Acc (Scalar a))

postulate
  nscanl' : ∀ {A} {n}
          → (A → A → A)
          → A
          → NVector n A
          → (NVector n A × NScalar A)

-- scanl1 :: Elt a
--        => (Exp a -> Exp a -> Exp a)
--        -> Acc (Vector a)
--        -> Acc (Vector a)

postulate 
  nscanl1 : ∀ {A}{n}
          → (A → A → A)
          → NVector n A
          → NVector n A

-- scanr :: Elt a
--       => (Exp a -> Exp a -> Exp a)
--       -> Exp a
--       -> Acc (Vector a)
--       -> Acc (Vector a)

postulate 
  nscanr : ∀ {A}{n}
         → (A → A → A)
         → A
         → NVector n A
         → NVector (suc n) A

-- scanr' :: Elt a
--        => (Exp a -> Exp a -> Exp a)
--        -> Exp a
--        -> Acc (Vector a)
--        -> (Acc (Vector a), Acc (Scalar a))

postulate 
  nscanr' : ∀ {A}{n}
          → (A → A → A)
          → A
          → NVector n A
          → (NVector n A × NScalar A)

-- scanr1 :: Elt a
--        => (Exp a -> Exp a -> Exp a)
--        -> Acc (Vector a)
--        -> Acc (Vector a)

postulate
  nscanr1 : ∀ {A}{n}
          → (A → A → A)
          → NVector n A
          → NVector n A

-- The combination function must be /associative/.  Eltents that are mapped to
-- the magic value 'ignore' by the permutation function are being dropped.
--
-- permute :: (Shape ix, Shape ix', Elt a)
--         => (Exp a -> Exp a -> Exp a)    -- ^combination function
--         -> Acc (Array ix' a)            -- ^array of default values
--         -> (Exp ix -> Exp ix')          -- ^permutation
--         -> Acc (Array ix  a)            -- ^permuted array
--         -> Acc (Array ix' a)
-- permute = Acc $$$$ Permute

postulate 
  npermute : ∀ {A}{sh}{sh'}
           → (A → A → A)
           → NArray sh' A
           → (NIndex sh → NIndex sh')   -- NArray sh (NIndex sh')
           → NArray sh A
           → NArray sh' A

-- |Backward permutation 
--
-- backpermute :: (Shape ix, Shape ix', Elt a)
--             => Exp ix'                  -- ^shape of the result array
--             -> (Exp ix' -> Exp ix)      -- ^permutation
--             -> Acc (Array ix  a)        -- ^permuted array
--             -> Acc (Array ix' a)
-- backpermute = Acc $$$ Backpermute

-- shape of result is implicit in the type!
postulate 
  nbackpermute : ∀ {A}{sh}{sh'}
               → (NIndex sh' → NIndex sh)
               → NArray sh A
               → NArray sh' A
