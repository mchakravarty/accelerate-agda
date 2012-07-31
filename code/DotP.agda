module DotP where

open import Data.Nat using (ℕ)
open import AccLib

-- * agda example for dot product with accelerate
dotp : ∀ {E : Element} {{p : IsNumeric E}} {n : ℕ} → PreVector n E → PreVector n E → Scalar E
dotp{E} xs ys = 
  let xs' = use xs
      ys' = use ys
  in
  fold _+_ ("0" ::: E) (zipWith _*_ xs' ys')


