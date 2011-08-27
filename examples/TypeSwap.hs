{-# LANGUAGE RankNTypes #-}
module TypeSwap(
m,
m'
) where

m :: forall b a. (a -> b) -> [a] -> [b]
m _ [] = []
m f (x:xs) = f x : m f xs

m' :: forall a b. (a -> b) -> [a] -> [b]
m' _ [] = []
m' f (x:xs) = f x : m' f xs
