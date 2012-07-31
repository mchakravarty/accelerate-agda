module ParsedString where

open import Data.Bool
open import Data.Char
open import Data.List
open import Data.List.All
open import Data.Nat
open import Data.Product
open import Data.String hiding (_==_)
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Relation.Binary.PropositionalEquality

open import Parsing


record Parsed (p : String → Bool) : Set where
  field
    s : String
    yes : T (p s)

il : Parsed isIntLiteral
il = record { s = "44" }

ni : Parsed isIntLiteral
ni = record { s = "xxx" }

ne : Parsed isIntLiteral
ne = record { s = "" }

f : (s : String) → {yes : T (isIntLiteral s)} → String
f s {yes} = let pp : Parsed isIntLiteral
                pp = record { s = s ; yes = yes }
            in  "ysy"

f0 = f "0"
fx = f "x"

record Parsed' (p : String → Bool) : Set where
  field
    s : String
    yes : p s ≡ true

g : (s : String) (p : String → Bool) {prf : p s ≡ true} → Parsed' p
g s p {prf} with p s | inspect p s
g s p {refl} | true | Reveal_is_.[_] eq = record { s = s; yes = eq }
g s p {()} | false | Reveal_is_.[_] eq 

g0 = g "0" isIntLiteral
gx = g "x" isIntLiteral

h : (s : String) {prf : isIntLiteral s ≡ true} → Parsed' isIntLiteral
h s {prf} with isIntLiteral s | inspect isIntLiteral s
h s {refl} | true | Reveal_is_.[_] eq = record { s = s; yes = eq }
h s {()} | false | Reveal_is_.[_] eq 

h0 = h "0"
hx = h "x"


k : (s : String) (prf : T (isIntLiteral s)) → Parsed isIntLiteral
k s prf = record { s = s ; yes = prf } 

k0 = k "0" tt
-- kx = k "x" tt

data PSTR : Bool → Set where
  pstr : (p : String → Bool) (s : String) → PSTR (p s)

ISP = PSTR true



digit : Char → Set
digit c = let cn = toNat c in (digit0 ≤ cn) × (cn ≤ digit9)

pdigit : (c : Char) → let cn = toNat c in (digit0 ≤ cn) × (cn ≤ digit9)
pdigit c = {!!}

record PS : Set where
  field
    s : String
    p : All digit (toList s)



{-
ps : PS
ps = record { s = "44"; p = (digit '4') ∷ (digit '4') ∷ [] }
-}