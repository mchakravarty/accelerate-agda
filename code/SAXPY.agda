module SAXPY where

open import Data.Nat using (ℕ)
open import AccLib

saxpy : ∀ {E : Element} {{p : IsNumeric E}} {n : ℕ}
      → Exp E → PreVector n E → PreVector n E → Vector n E
saxpy α xs ys =
  let
    xs' = use xs
    ys' = use ys
  in
  zipWith (λ x y → (α * x) + y) xs' ys'
