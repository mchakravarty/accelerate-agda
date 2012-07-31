module Main2 where

open import IO.Primitive
open import Foreign.Haskell

-- open import Data.Nat
open import Data.String
open import Data.Vec hiding (_>>=_; [_])

open import Relation.Binary.PropositionalEquality hiding ([_])

open import AccLib
open import DotP
open import SASUM
open import SAXPY

infixl 1 _>>_

_>>_ : ∀ {ℓ a b} → IO{ℓ} a → IO{ℓ} b → IO{ℓ} b
ma >> mb = ma >>= λ _ → mb

main : IO Unit
main =
  putStrLn (toCostring "dot product")
  >>
  let a1 = ("17" ∷ "4" ∷ []) asArrayOf Int
      a2 = ("1"  ∷ "1" ∷ []) asArrOf Int , [ 2 ] , refl
      b2 = ("1"  ∷ "1" ∷ "2"  ∷ "2" ∷ []) asArrOf Int , [ 2 , 2 ] , refl
      c2 = ("1"  ∷ "2" ∷ "3"  ∷ "4" ∷ "5"  ∷ "6" ∷ "7" ∷ "8" ∷ [])
           asArrOf Int , [ 2 , 2 , 2 ] , refl
      a3 = dotp a1 a2
      a4 = run a3
  in
  putStrLn (toCostring (showArray a4))
  >>
  putStrLn (toCostring "sum of absolute values")
  >>
  let a1 = ("3.14159265" ∷ "-2.7182818" ∷ "-5e-1" ∷ []) asArrayOf Float
      a2 = sasum a1
      a3 = run a2
  in
  putStrLn (toCostring (showArray a3))
  >>
  putStrLn (toCostring "linear combination")
  >>
  let a1 = ("1.1" ∷ "2.2" ∷ "3.3" ∷ []) asArrayOf Float
      a2 = ("1.5" ::: Float)
      a3 = saxpy a2 a1 a1
      a4 = run a3
  in
  putStrLn (toCostring (showArray a4))