module Parsing-wojtek where

open import Data.Char
open import Data.String
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Unit

startsWithZero : String → Bool
startsWithZero s with toList s
startsWithZero s | [] = false
startsWithZero s | x ∷ xs with Data.Char._≟_ x '0'
startsWithZero s | x ∷ xs | yes p = true
startsWithZero s | x ∷ xs | no ¬p = false

getType : String → Set
getType s with startsWithZero s
... | true  = String
... | false = ⊤

stringLit : (s : String) → getType s
stringLit s with startsWithZero s
... | true  = s
... | false = tt

s : String
s = stringLit "0123"

{---Type error:
s2 : String
s2 = stringLit "123"  -- ⊤ ≠ String
--}
