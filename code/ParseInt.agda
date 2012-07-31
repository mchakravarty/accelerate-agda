module ParseInt where

open import Data.Bool
open import Data.Char
open import Data.List
open import Data.Nat
open import Data.String
open import Data.Unit hiding (_≤?_)
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality

isIntLit : String → Bool
isIntLit xs = not (null xl) ∧ check xl
  where
  xl = toList xs
  check : List Char → Bool
  check [] = true
  check (x ∷ xs) with toNat x
  ... | xn with toNat '0' ≤? xn | xn ≤? toNat '9'
  ... | yes p | yes q = check xs
  ... | yes p | no ¬q = false
  ... | no ¬p | yes q = false
  ... | no ¬p | no ¬q = false

data Parsed (p : String → Bool) : String → Set where
  ok : (s : String) → T (p s) → Parsed p s

p≡true : ∀ {p} → T p → p ≡ true
p≡true {true} tp = refl
p≡true {false} ()

absurd : ∀ s → isIntLit s ≡ false → ¬ (Parsed isIntLit s)
absurd s p (ok .s Tp) with p≡true Tp
... | ¬p rewrite p with ¬p
... | ()

intLit? : (s : String) → Dec (Parsed isIntLit s)
intLit? s with isIntLit s | inspect isIntLit s
intLit? s | true | Reveal_is_.[_] eq = yes (ok s (subst T (sym eq) tt))
intLit? s | false | Reveal_is_.[_] eq = no (absurd s eq)

i0 : intLit? "0" ≡ yes (ok "0" tt)
i0 = refl

ix : intLit? "x" ≡ no (absurd "x" refl)
ix = refl
