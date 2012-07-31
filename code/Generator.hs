module Generator where

import qualified Data.Array.Accelerate as A
import Accel
import System.Random

fixedArray111 :: IO (Array A.DIM1 Int)
fixedArray111 = return (fromList' [1, 1, 1])

randomArray52 :: IO (Array A.DIM1 Int)
randomArray52 = randomArray 52

randomArray :: Int -> IO (Array A.DIM1 Int)
randomArray n = do
  xs <- randomList n
  return (fromList' xs)

randomList :: Int -> IO [Int]
randomList 0 = 
  return []
randomList n = do
  xs <- randomList (n-1)
  x <- randomInt
  return (x : xs)

randomInt = getStdRandom (randomR (minBound,maxBound))