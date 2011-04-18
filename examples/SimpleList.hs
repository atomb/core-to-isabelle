module SimpleList
  where

import Prelude ()

data List a = Nil | Cons a (List a)

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)
