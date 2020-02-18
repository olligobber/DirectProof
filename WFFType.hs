{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

module WFFType (
    Not,
    type (/\)(),
    type (\/)(),
    type (-->)(),
    type (<->)()
) where

infix 5 /\
infix 5 \/
infix 5 -->
infix 5 <->

data (/\) a b
data (\/) a b
data (-->) a b
data (<->) a b
data Not a
