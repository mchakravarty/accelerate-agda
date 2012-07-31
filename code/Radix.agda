module Radix where

-- radix sort

open import Data.Nat renaming (_+_ to _+ℕ_)
open import Data.List hiding (zipWith; zip) renaming (map to listmap; [_] to [[_]])
open import Function
open import AccLib

-- support functions
enumFromTo : (m : ℕ) → (n : ℕ) → (p : m ≤ n) → List ℕ
enumFromTo zero zero p = zero ∷ []
enumFromTo zero (suc n) z≤n = zero ∷ listmap suc (enumFromTo zero n z≤n)
enumFromTo (suc n) zero ()
enumFromTo (suc n) (suc n') (s≤s m≤n) = listmap suc (enumFromTo n n' m≤n)

-- let's only support integers
passes : ℕ
passes = 32

passes' : Exp Int
passes' = constant (toHsInt passes) 

radix' : Exp Int → Exp Int → Exp Int
radix' i x = (x shiftR i) & ("1" ::: Int)

minBound : Exp Int
minBound = "-2147483648" ::: Int

radix : Exp Int → Exp Int → Exp Int
radix i e = if (i == (passes' - ("1" ::: Int))) then radix' i (e xor minBound) else radix' i e

rSortBy : ∀ {E n} → (Exp E → Exp Int) → PreVector n E → Vector n E
rSortBy {E}{n} rdx arr =
  foldr _>->_ id (listmap radixPass (enumFromTo 0 (passes ∸ 1) z≤n)) (use arr)
  where
  nn : Exp Int
  nn = constant (toHsInt (n ∸ 1))
  deal : Exp Int → Exp (Pair Int Int) → Exp Int
  deal f x = if f == ("0" ::: Int) then fst x else snd x
  radixPass : ℕ → Array E [ n ] → Array E [ n ]
  radixPass k v = 
    let
      flags = map (radix (constant (toHsInt k)) ∘ rdx) v
      idown = prescanl _+_ ("0" ::: Int) (map (_xor_ ("1" ::: Int)) flags)
      iup   = map (_-_ nn) (prescanr _+_ ("0" ::: Int) flags)
      index = zipWith deal flags (zip idown iup)
    in
      permute const v (λ ix → index1 (index ! ix)) v
