module Main where

open import IO.Primitive
open import Foreign.Haskell

open import Data.Nat
open import Data.String
open import AccLib
open import DotP


{-# IMPORT Generator #-}
{-# IMPORT Accel #-}

postulate
  randomArray : IO (HsArray HsDIM1 HsInt)
  fixedArray  : IO (HsArray HsDIM1 HsInt) 
{-# COMPILED randomArray Generator.randomArray52 #-}
{-# COMPILED fixedArray Generator.fixedArray111 #-}

main : IO Unit
main = fixedArray >>= λ a1 → fixedArray >>= 
  (λ a2 →
     let p1 : _
         p1 = PA{Int}{[ 3 ]} a1
         p2 : _
         p2 = PA{Int}{[ 3 ]} a2
         p3 : _
         p3 = dotp p1 p2
         p4 : _
         p4 = run p3
     in putStrLn (toCostring (showArray p4)))
