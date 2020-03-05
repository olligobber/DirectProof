{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}

module WFFType (
    Not,
    type (/\)(),
    type (\/)(),
    type (-->)(),
    type (<->)(),
    BinOp(getop, extract),
    AlgOp
) where

import WFF (WFF(..))

infix 5 /\
infix 5 \/
infix 5 -->
infix 5 <->

data (/\) a b = And (forall x. WFF x -> WFF x -> WFF x)
data (\/) a b = Or (forall x. WFF x -> WFF x -> WFF x)
data (-->) a b = Imp (forall x. WFF x -> WFF x -> WFF x)
data (<->) a b = Equ (forall x. WFF x -> WFF x -> WFF x)
data Not a

class BinOp b where
    getop :: b x y
    extract :: b x y -> (forall a. WFF a -> WFF a -> WFF a)

instance BinOp (/\) where
    getop = And (:&:)
    extract (And x) = x

instance BinOp (\/) where
    getop = Or (:|:)
    extract (Or x) = x

instance BinOp (-->) where
    getop = Imp (:>:)
    extract (Imp x) = x

instance BinOp (<->) where
    getop = Equ (:=:)
    extract (Equ x) = x

class (BinOp b, BinOp c) => AlgOp b c | b -> c, c -> b

instance AlgOp (/\) (\/)

instance AlgOp (\/) (/\)
