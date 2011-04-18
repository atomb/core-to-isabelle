module Tree where

data Tree m = Tip | Branch (m (Forest m))

data Forest m = F (Tree m)