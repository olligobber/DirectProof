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

-- Type level WFFs

infix 5 /\
infix 5 \/
infix 5 -->
infix 5 <->

data (/\) a b = And
data (\/) a b = Or
data (-->) a b = Imp
data (<->) a b = Equ
data Not a

-- Binary operations class, used for lifts
class BinOp b where
    getop :: b x y
    extract :: b x y -> (forall a. WFF a -> WFF a -> WFF a)

instance BinOp (/\) where
    getop = And
    extract And = (:&:)

instance BinOp (\/) where
    getop = Or
    extract Or = (:|:)

instance BinOp (-->) where
    getop = Imp
    extract Imp = (:>:)

instance BinOp (<->) where
    getop = Equ
    extract Equ = (:=:)

-- Algebraic operations class, used for algebraic equivalences
class (BinOp b, BinOp c) => AlgOp b c | b -> c, c -> b

instance AlgOp (/\) (\/)

instance AlgOp (\/) (/\)
