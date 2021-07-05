module Chapter1 where

import Prelude hiding (abs)

{-@ abs :: Nat -> Nat @-}
abs :: Int -> Int
abs x
  | x < 0     = - x
  | otherwise = x

{-@ sub :: i : Nat -> { j : Nat | i >= j } -> Nat @-}
sub :: Int -> Int -> Int
sub i j = i - j

{-@ halve :: i : Int -> { j : (Int, Int) | i == fst j + snd j } @-}
halve :: Int -> (Int, Int)
halve i = (j, j + r)
  where
    j = i `div` 2
    r = i `mod` 2