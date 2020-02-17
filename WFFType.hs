{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

module WFFType (
    Not,
    type (/\)(),
    type (\/)(),
    type (-->)(),
    type (<->)()
) where

data And a b
data Or a b
data Implies a b
data Equivalent a b
data Not a

type (/\) = And
type (\/) = Or
type (-->) = Implies
type (<->) = Equivalent
