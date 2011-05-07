module Foo where

data Foo a = Foo !a

newtype Foo' a = Foo' a

unfoo (Foo x) = x
unfoo' (Foo' x) = x

