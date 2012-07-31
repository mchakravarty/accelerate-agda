module Filter where

open import Data.Nat using (ℕ; suc; _>_) renaming (_*_ to _*ℕ_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to _,,_)
open import Function
open import AccLib

{-
-- * agda example for filtering with accelerate
-- the problem is that the size, m, of the result vector is unknown.
-- all we could say is that m ≤ n, the number of times that p is
-- true on the elements of the input vector.
filterAcc : ∀ {E : Element} {{p : IsNumeric E}} {n m : ℕ}
          → (Exp E → Exp Bool) → PreVector n E → Vector m E
filterAcc {E} p vec = 
  let
    arr           = use vec
    flags         = map (boolToInt ∘ p) arr
    targetIdx,len = scanl' _+_ ("0" ::: _) flags
    targetIdx     = proj₁ targetIdx,len
    len           : Scalar Int
    len           = proj₂ targetIdx,len 
    -- intention of the backpermute is just to create an array of the right type and 
    -- length to serve as default array for the permutation
    arr'          = backpermute{_}{_}{[ _ ]}{_}{_} {_}{_} (index1 (the len)) id arr
                    -- the offending argument is
                    -- {sh_res : Shape}
                    -- where the number of elements cannot be inferred
  in
    {!!}

{-
   I don't think that this can be completed.
   An alternative approach would be to represent a filtered array
   as an array of pairs of type (Bool, elt), where the first 
   component indicates whether the second is part of the array.
   This method avoids the need to create an array statically unknown
   size. The filtered array could also be represented as a segmented
   array with two segments, the first segment comprising the elements
   that properly belong to the array and second segment comprising
   the junk elements. The segmented approach has the advantage that
   the array operations can be more easily applied (?)
-}
-}

FArray : Element → Shape → Set
FArray E sh = Array (Pair Bool E) sh

FVector : ℕ → Element → Set
FVector n E = Vector n (Pair Bool E)

filter1 : ∀ {E : Element} {sh}
        → (Exp E → Exp Bool) → Array E sh → FArray E sh
filter1 {E}{n} p arr =
  map g arr
  where
  g : Exp E → Exp (Pair Bool E)
  g x = pair (p x) x

-- lifting of operations and constants
liftop0 : ∀ {E}
        → Exp E
        → Exp (Pair Bool E)
liftop0 e = pair (constant trueHs) e

liftop1 : ∀ {E}
        → (Exp E → Exp E)
        → (Exp (Pair Bool E) → Exp (Pair Bool E))
liftop1 f px = pair (fst px) (f (snd px))

liftop2 : ∀ {E}
        → (Exp E → Exp E → Exp E)
        → (Exp (Pair Bool E) → Exp (Pair Bool E) → Exp (Pair Bool E))
liftop2 f px py =
  pair (fst px && fst py)
       (if fst px then if fst py then f (snd px) (snd py) else snd px
                  else snd py)

-- normal form for filtered vectors
-- first segment: true, second segment: false
nf : ∀{n E} → FVector n E → FVector n E
nf vec with map (boolToInt ∘ fst) vec
... | trueFlags with scanl' _+_ ("0" ::: Int) trueFlags
... | trueTargets,nrTrue with proj₁ trueTargets,nrTrue
... | trueTargets with proj₂ trueTargets,nrTrue
... | nrTrue with map (boolToInt ∘ not ∘ fst) vec
... | falseFlags with proj₁ (scanl' _+_ (the nrTrue) falseFlags)
... | falseTargets =
    permute const vec g vec
  where
  g : Exp (ZC ZZ Int) → Exp (ZC ZZ Int)
  g ix with fst (vec ! ix)
  ... | tix = index1 (if tix then trueTargets ! ix else (falseTargets ! ix))
  -- this is an abuse of permute (cf comment in Accelerate example Filter.hs)
  -- unfortunately, it is not possible to implement it using generate because
  -- the index transformation cannot be phrased in terms of the result indexes

  -- the nf function may also return a segment descriptor ...

-- filtering on filtered arrays
ffilter : ∀ {E sh} → (Exp E → Exp Bool) → FArray E sh → FArray E sh
ffilter {E}{sh} f arr = 
  map g arr
  where 
  g : Exp (Pair Bool E) → Exp (Pair Bool E)
  g p = if f (snd p) then p else pair (constant falseHs) (snd p)

-- injection from unfiltered to filtered arrays (needed?)
inFArray : ∀ {E sh} → Array E sh → FArray E sh
inFArray {E}{sh} arr = map liftop0 arr

-- hmm, but we know that all pairs in the result have the form (true, ...)
ffold : ∀ {E sh n} → (Exp E → Exp E → Exp E) → Exp E → FArray E (sh :< n >) → FArray E sh
ffold {E}{sh}{n} f e farr =
  fold op unit farr
  where
  unit : Exp (Pair Bool E)
  unit = liftop0 e
  op : Exp (Pair Bool E) → Exp (Pair Bool E) → Exp (Pair Bool E)
  op px py = if (fst px) then
             (if (fst py) then pair (constant trueHs) (f (snd px) (snd py))
                         else px)
            else (if (fst py) then py
                             else unit)

-- ... but we can have our cake and eat it, too!
ffold' : ∀ {E sh n} → (Exp E → Exp E → Exp E) → Exp E → FArray E (sh :< n >) → Array E sh
ffold' {E}{sh}{n} f e farr =
  fold f e (map (λ p → if (fst p) then (snd p) else e) farr)

-- not so with fold1, where the combination function retains the pairs
ffold1 : ∀ {E sh n}
       → (Exp E → Exp E → Exp E)
       → FArray E (sh :< n >) → (p : size sh *ℕ n > 0) → FArray E sh
ffold1 {E} {sh} {n} f arr p = fold1 (liftop2 f) arr p 

fscanl : ∀ {E n}
      → (Exp E → Exp E → Exp E)
      → Exp E
      → FVector n E
      → FVector (suc n) E
fscanl f e vec = scanl (liftop2 f) (liftop0 e) vec

-- can get rid of the flags with fscanl', but not quite so effective
fscanl' : ∀ {E n}
      → (Exp E → Exp E → Exp E)
      → Exp E
      → FVector n E
      → Vector (suc n) E
fscanl' f e vec = 
  scanl f e (map (λ p → if (fst p) then (snd p) else e) vec)

fmap : ∀ {E F sh} → (Exp E → Exp F) → FArray E sh → FArray F sh
fmap f = map (λ p → pair (fst p) (f (snd p))) 
{-
-- maybe better with a  default target element;
-- otherwise the mapping function must be applied to *all* array elements;
-- the default could be provided as a {{...}} binding, depending on the type
fmap : ∀ {E F sh} → (Exp E → Exp F) → Exp F → FArray E sh → FArray F sh
fmap f d = map (λ p → if (fst p) then pair (constant trueHs) (f (snd p))
                                 else pair (constant falseHs) d) 
-}

-- zipWith requires some reordering and it is totally unclear how to define
-- this reordering for multi dimensional arrays
fzipWith : ∀ {A B C n} → (Exp A → Exp B → Exp C) → FVector n A → FVector n B → FVector n C
fzipWith {A}{B}{C} f va vb with nf va | nf vb
... | nva | nvb = zipWith g nva nvb
  where
  g : Exp (Pair Bool A) → Exp (Pair Bool B) → Exp (Pair Bool C)
  g ea eb = pair (fst ea && fst eb) (f (snd ea) (snd eb))
  -- not sure, if it's a good idea to apply f to all elements
  -- at the very least, it is inefficient (or is it?)



-- a segmented version
FSVector : ℕ → Element → Set
FSVector n E = Vector 2 Int × Vector n E

nfs : ∀{n E} → FVector n E → FSVector n E
nfs {n} vec with map (boolToInt ∘ fst) vec
... | trueFlags with scanl' _+_ ("0" ::: Int) trueFlags
... | trueTargets,nrTrue with proj₁ trueTargets,nrTrue
... | trueTargets with the (proj₂ trueTargets,nrTrue)
... | nrTrue with map (boolToInt ∘ not ∘ fst) vec
... | falseFlags with proj₁ (scanl' _+_ nrTrue falseFlags)
... | falseTargets with backpermute (index1 (constant (toHsInt n))) g vec
  where
  g : Exp (ZC ZZ Int) → Exp (ZC ZZ Int)
  g ix with fst (vec ! ix)
  ... | tix = index1 (if tix then trueTargets ! ix else (falseTargets ! ix))
... | resultVec = strongGenerate [ 2 ] ((λ y →
                                             if y == ("0" ::: FInt 2) then nrTrue else
                                             (constant (toHsInt n) - nrTrue)) ∘ unindex1F)
                  ,, map snd resultVec

--------------------------------------------------------------------------------------
-- another design option altogether would be to delay the computation of the predicate
-- alltogether

FilteredArray : Element → Shape → Set
FilteredArray E sh = (Exp E → Exp Bool) × Array E sh

FilteredVector : ℕ → Element → Set
FilteredVector n E = (Exp E → Exp Bool) × Vector n E

filterF : ∀ {sh E} → (Exp E → Exp Bool) → Array E sh → FilteredArray E sh
filterF p v = p ,, v

filterFF : ∀ {sh E} → (Exp E → Exp Bool) → FilteredArray E sh → FilteredArray E sh
filterFF p fv = (λ b → p b && proj₁ fv b) ,, proj₂ fv

-- etc etc, could be fused into a fold
