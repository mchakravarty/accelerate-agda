module SASUM where

open import Data.Nat using (ℕ)
open import AccLib

-- * agda example for sum of absolute values
sasum : ∀ {E : Element} {{p : IsNumeric E}} {n : ℕ} → PreVector n E → Scalar E
sasum{E} xs =
  fold _+_ ("0" ::: E) (map abs (use xs))
