module Parsing-allais where

open import Data.Char
open import Data.List
open import Data.String hiding (_==_)

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat

open import Data.Product

open import Relation.Binary.PropositionalEquality

isDigit : Char → Bool
isDigit c = (c == '0') ∨ (c == '1') ∨ (c == '2') ∨ (c == '3') ∨
            (c == '4') ∨ (c == '5') ∨ (c == '6') ∨ (c == '7') ∨
            (c == '8') ∨ (c == '9')

getDigit : ∀ (c : Char) (q : isDigit c ≡ true) → ℕ
getDigit c q with c == '0' | c == '1' | c == '2' | c == '3' | c == '4' |
  c == '5' | c == '6' | c == '7' | c == '8' | c == '9'
... | true | _ | _ | _ | _ | _ | _ | _ | _ | _ = 0
... | _ | true | _ | _ | _ | _ | _ | _ | _ | _ = 1
... | _ | _ | true | _ | _ | _ | _ | _ | _ | _ = 2
... | _ | _ | _ | true | _ | _ | _ | _ | _ | _ = 3
... | _ | _ | _ | _ | true | _ | _ | _ | _ | _ = 4
... | _ | _ | _ | _ | _ | true | _ | _ | _ | _ = 5
... | _ | _ | _ | _ | _ | _ | true | _ | _ | _ = 6
... | _ | _ | _ | _ | _ | _ | _ | true | _ | _ = 7
... | _ | _ | _ | _ | _ | _ | _ | _ | true | _ = 8
... | _ | _ | _ | _ | _ | _ | _ | _ | _ | true = 9
getDigit c () | false | false | false | false | false | false | false | false | false | false

getDigits : ∀ (ns : List Char) (q : all isDigit ns ≡ true) → List ℕ
getDigits [] q = []
getDigits (n ∷ ns) q with isDigit n | getDigit n
getDigits (n ∷ ns) q | true | f = (f refl) ∷ (getDigits ns q)
getDigits (n ∷ ns) () | false | f

DigitsToNat-rec : List ℕ → ℕ → ℕ
DigitsToNat-rec [] acc = acc
DigitsToNat-rec (n ∷ ns) acc = DigitsToNat-rec ns (n + 10 * acc)

DigitsToNat : List ℕ → ℕ
DigitsToNat ns = DigitsToNat-rec ns 0

record ℕString : Set where
  constructor ⟨_,_⟩
  field
    val : String
    prf : all isDigit (toList val) ≡ true

Natify : ∀ (s : ℕString) → ℕ
Natify ⟨ val , prf ⟩ = DigitsToNat (getDigits (toList val) prf)

t : ℕ
t = Natify ⟨ "1234" , refl ⟩

f : ℕ
f = Natify ⟨ "hello world!" , refl ⟩