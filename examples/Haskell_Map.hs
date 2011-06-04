module Map where

import Prelude ()

data List a = Nil | Cons a (List a)

map :: (a -> b) -> List a -> List b
map f Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

{-
class Functor f where
  fmap :: (a -> b) -> f a -> f b

instance Functor List where
  fmap = map
-}
{-
data Bool = True | False
newtype NotBool = Ninja Bool
notTrue = Ninja True
-}