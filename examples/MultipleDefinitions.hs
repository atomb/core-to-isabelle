module MulitpleDefinitions where

import Prelude ()

data List a = Nil | Cons a (List a)

data Color = Red | Green | Blue

data Maybe a = Nothing | Just a

data Unit = Unit

data Bool = True | False

map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs

zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
zipWith f _      _      = []

undefined :: a
undefined = undefined

head :: [a] -> a
head (x:_) = x
head _     = undefined

fromJust :: Maybe a -> a
fromJust (Just x) = x
fromJust _        = undefined
