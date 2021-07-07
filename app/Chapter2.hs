module Chapter2 where

import Prelude hiding (map, length, take)


data List a = Nil | Cons a (List a)
  deriving (Show)

infixr 5 `Cons`

list1 :: List Int
list1 = 1 `Cons` 2 `Cons` 3 `Cons` Nil

{-@ list2 :: List Nat @-}
list2 :: List Int
list2 = 1 `Cons` 2 `Cons` 3 `Cons` Nil

{-@ measure length @-}
{-@ data List [length] @-}
{-@ length :: List a -> Nat @-}
length :: List a -> Int
length Nil = 0
length (x `Cons` xs) = 1 + length xs

{-@ map :: (a -> b) -> listA: List a -> {listB: List b | length listA == length listB} @-}
map :: (a -> b) -> List a -> List b
map _ Nil           = Nil
map f (x `Cons` xs) = f x `Cons` map f xs

{-@ interleave :: xs : List a -> ys : List a -> List a / [length xs + length ys] @-}
interleave :: List a -> List a -> List a
interleave Nil           ys  = ys
interleave xs            Nil = xs
interleave (x `Cons` xs) ys  = x `Cons` interleave ys xs

{-@ take :: i : Nat -> List a -> { ys : List a | length ys <= i } @-}
take :: Int -> List a -> List a
take _ Nil         = Nil
take 0 _           = Nil
take i (Cons x xs) =
  x `Cons` take (i - 1) xs