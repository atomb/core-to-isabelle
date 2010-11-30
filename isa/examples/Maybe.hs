module Maybe
  where

import Prelude ()

data Maybe a = Nothing | Just a

map :: (a -> b) -> Maybe a -> Maybe b
map f Nothing = Nothing
map f (Just x) = Just (f x)
