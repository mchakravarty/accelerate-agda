module Parsing where

open import Data.Bool
open import Data.Char
open import Data.Nat
open import Data.List
open import Data.String hiding (_==_)

le : ℕ → ℕ → Bool
le zero y = true
le (suc n) zero = false
le (suc n) (suc n') = le n n'

digit0 : ℕ
digit0 = toNat '0'

digit9 : ℕ
digit9 = toNat '9'

isDigit : Char → Bool
isDigit c = let cn = toNat c in (le digit0 cn) ∧ (le cn digit9)

isDigits : List Char → Bool
isDigits cs = foldr (λ x b → isDigit x ∧ b) true cs

empty : ∀ {ℓ E} → List{ℓ} E → Bool
empty [] = true
empty (x ∷ xs) = false

isIntLiteral' : List Char → Bool
isIntLiteral' [] = false
isIntLiteral' (x ∷ xs) = ((x == '+') ∨ (x == '-') ∨ isDigit x) ∧ isDigits xs

isIntLiteral : String → Bool
isIntLiteral s = isIntLiteral' (toList s)

data FLState : Set where
  FL0 : FLState
  FL1 : FLState
  FL2 : FLState
  FL3 : FLState
  FL4 : FLState
  FL5 : FLState
  FL6 : FLState

isFinal : FLState → Bool
isFinal FL2 = true
isFinal FL3 = true
isFinal FL6 = true
isFinal _ = false

isFloatLiteral' : FLState → List Char → Bool
isFloatLiteral' fs [] = isFinal fs
isFloatLiteral' FL0 (x ∷ xs) =
  if (x == '+') ∨ (x == '-') then isFloatLiteral' FL1 xs else
  if (x == '.') then isFloatLiteral' FL3 xs else
  if isDigit x then isFloatLiteral' FL2 xs else false
isFloatLiteral' FL1 (x ∷ xs) = -- seen sign
  if isDigit x then isFloatLiteral' FL2 xs else 
  if (x == '.') then isFloatLiteral' FL3 xs else false
isFloatLiteral' FL2 (x ∷ xs) = 
  if isDigit x then isFloatLiteral' FL2 xs else
  if x == '.' then isFloatLiteral' FL3 xs else 
  if (x == 'e') ∨ (x == 'E') then isFloatLiteral' FL4 xs else false
isFloatLiteral' FL3 (x ∷ xs) = -- seen dot; skip digits
  if isDigit x then isFloatLiteral' FL3 xs else 
  if (x == 'e') ∨ (x == 'E') then isFloatLiteral' FL4 xs else false
isFloatLiteral' FL4 (x ∷ xs) = -- seen E
  if (x == '+') ∨ (x == '-') then isFloatLiteral' FL5 xs else
  if isDigit x then isFloatLiteral' FL6 xs else false
isFloatLiteral' FL5 (x ∷ xs) = -- seen E[+-]
  if isDigit x then isFloatLiteral' FL6 xs else false
isFloatLiteral' FL6 (x ∷ xs) =
  if isDigit x then isFloatLiteral' FL6 xs else false

isFloatLiteral : String → Bool
isFloatLiteral s = isFloatLiteral' FL0 (toList s)

isBoolLiteral : String → Bool
isBoolLiteral "true" = true
isBoolLiteral "false" = true
isBoolLiteral _ = false
