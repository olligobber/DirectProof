{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module WFFType (
    Not,
    type (/\)(),
    type (\/)(),
    type (-->)(),
    type (<->)(),
    BinOp(getop),
    AlgOp
) where

import WFF (WFF(..), BinaryOperator)

-- Type level WFFs
infix 5 /\
infix 5 \/
infix 5 -->
infix 5 <->
data (/\) a b
data (\/) a b
data (-->) a b
data (<->) a b
data Not a

-- Binary operations class, used for lifts of proofs
class BinOp (b :: * -> * -> *) where
    getop :: BinaryOperator

instance BinOp (/\) where
    getop = (:&:)

instance BinOp (\/) where
    getop = (:|:)

instance BinOp (-->) where
    getop = (:>:)

instance BinOp (<->) where
    getop = (:=:)

-- Algebraic operations class, used for algebraic equivalence rules
class (BinOp b, BinOp c) => AlgOp b c | b -> c, c -> b

instance AlgOp (/\) (\/)

instance AlgOp (\/) (/\)
