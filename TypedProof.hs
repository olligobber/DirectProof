{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}

module TypedProof (
    -- types and conversions
    type (|-)(), type (===)(), toTyped, invert, toPlain
    --lifts
    liftAnd1, liftAnd2, liftOr1, liftOr2, liftImplies1, liftImplies2,
    liftEquiv1, liftEquiv2, liftNot,
    -- equivalence rules
    deMorgans1, deMorgans2, commutationOr, commutationAnd, associationOr,
    associationAnd, distribution1, distribution2, doubleNegation,
    transposition, defImplication, matEquivalence, defEquivalence, exportation,
    idempotenceOr, idempotenceAnd,
    -- deduction rules
    simplification, addition
) where

import Prelude hiding (id, (.)) -- Control.Category redefines these
import Data.Text (Text)
import Control.Category

import Proof
import ReLabel (reLabel)
import WFF (WFF(..))
import qualified WFF as W
import WFFType

-- Proof symbols
infix 2 |-
infix 2 ===

-- A one directional proof
newtype (|-) start end = TypedProof { getPlain :: Proof Integer}

instance Category (|-) where
    id = TypedProof $ Proof [Prop 1] []
    (TypedProof p2) . (TypedProof p1) = TypedProof $ reLabel $ compose p1 p2

-- Two directional proof
newtype (===) a b = IsoProof { toTyped :: a |- b }

instance Category (===) where
    id = IsoProof id
    IsoProof p2 . IsoProof p1 = IsoProof $ p2 . p1

invert :: a === b -> b === a
invert (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ Proof
    (reverse $ formulas p)
    (reverse $ reasons p)

-- Lift proofs as subformulas

liftAnd1 :: a === b -> a /\ c === b /\ c
liftAnd1 (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ reLabel $
    mapWFF (:&: Prop Nothing) $ Just <$> p

liftAnd2 :: a === b -> c /\ a === c /\ b
liftAnd2 (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ reLabel $
    mapWFF (Prop Nothing :&:) $ Just <$> p

liftOr1 :: a === b -> a \/ c === b \/ c
liftOr1 (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ reLabel $
    mapWFF (:|: Prop Nothing) $ Just <$> p

liftOr2 :: a === b -> c \/ a === c \/ b
liftOr2 (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ reLabel $
    mapWFF (Prop Nothing :|:) $ Just <$> p

liftImplies1 :: a === b -> a --> c === b --> c
liftImplies1 (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ reLabel $
    mapWFF (:>: Prop Nothing) $ Just <$> p

liftImplies2 :: a === b -> c --> a === c --> b
liftImplies2 (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ reLabel $
    mapWFF (Prop Nothing :>:) $ Just <$> p

liftEquiv1 :: a === b -> a <-> c === b <-> c
liftEquiv1 (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ reLabel $
    mapWFF (:=: Prop Nothing) $ Just <$> p

liftEquiv2 :: a === b -> c <-> a === c <-> b
liftEquiv2 (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ reLabel $
    mapWFF (Prop Nothing :=:) $ Just <$> p

liftNot :: a === b -> Not a === Not b
liftNot (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ mapWFF Not p

-- Equivalence rules

deMorgans1 :: Not (a /\ b) === Not a \/ Not b
deMorgans1 = IsoProof $ TypedProof $ Proof
    [Not $ Prop 1 :&: Prop 2, Not (Prop 1) :|: Not (Prop 2)]
    ["De Morgan's"]

deMorgans2 :: Not (a \/ b) === Not a /\ Not b
deMorgans2 = IsoProof $ TypedProof $ Proof
    [Not $ Prop 1 :|: Prop 2, Not (Prop 1) :&: Not (Prop 2)]
    ["De Morgan's"]

commutationOr :: a \/ b === b \/ a
commutationOr = IsoProof $ TypedProof $ Proof
    [Prop 1 :|: Prop 2, Prop 2 :|: Prop 1]
    ["Commutation"]

commutationAnd :: a /\ b === b /\ a
commutationAnd = IsoProof $ TypedProof $ Proof
    [Prop 1 :&: Prop 2, Prop 2 :&: Prop 1]
    ["Commutation"]

associationOr :: a \/ (b \/ c) === (a \/ b) \/ c
associationOr = IsoProof $ TypedProof $ Proof
    [Prop 1 :|: (Prop 2 :|: Prop 3), (Prop 1 :|: Prop 2) :|: Prop 3]
    ["Association"]

associationAnd :: a /\ (b /\ c) === (a /\ b) /\ c
associationAnd = IsoProof $ TypedProof $ Proof
    [Prop 1 :&: (Prop 2 :&: Prop 3), (Prop 1 :&: Prop 2) :&: Prop 3]
    ["Association"]

distribution1 :: a /\ (b \/ c) === (a /\ b) \/ (a /\ c)
distribution1 = IsoProof $ TypedProof $ Proof
    [Prop 1 :&: (Prop 2 :|: Prop 3), (Prop 1 :&: Prop 2) :|: (Prop 1 :&: Prop 3)]
    ["Distribution"]

distribution2 :: a \/ (b /\ c) === (a \/ b) /\ (a \/ c)
distribution2 = IsoProof $ TypedProof $ Proof
    [Prop 1 :|: (Prop 2 :&: Prop 3), (Prop 1 :|: Prop 2) :&: (Prop 1 :|: Prop 3)]
    ["Distribution"]

doubleNegation :: a === Not (Not a)
doubleNegation = IsoProof $ TypedProof $ Proof
    [Prop 1, Not $ Not $ Prop 1]
    ["Double Negation"]

transposition :: a --> b === Not b --> Not a
transposition = IsoProof $ TypedProof $ Proof
    [Prop 1 :>: Prop 2, Not (Prop 2) :>: Not (Prop 1)]
    ["Transposition"]

defImplication :: a --> b === Not a \/ b
defImplication = IsoProof $ TypedProof $ Proof
    [Prop 1 :>: Prop 2, Not (Prop 1) :|: Prop 2]
    ["Definition of Implication"]

matEquivalence :: a <-> b === (a --> b) /\ (b --> a)
matEquivalence = IsoProof $ TypedProof $ Proof
    [Prop 1 :=: Prop 2, (Prop 1 :>: Prop 2) :&: (Prop 2 :>: Prop 1)]
    ["Material Equivalence"]

defEquivalence :: a <-> b === (a /\ b) \/ (Not a /\ Not b)
defEquivalence = IsoProof $ TypedProof $ Proof
    [Prop 1 :=: Prop 2, (Prop 1 :&: Prop 2) :|: (Not (Prop 1) :&: Not (Prop 2))]
    ["Definition of Equivalence"]

exportation :: (a /\ b) --> c === a --> (b --> c)
exportation = IsoProof $ TypedProof $ Proof
    [(Prop 1 :&: Prop 2) :>: Prop 3, Prop 1 :>: (Prop 2 :>: Prop 3)]
    ["Exportation"]

idempotenceOr :: a === a \/ a
idempotenceOr = IsoProof $ TypedProof $ Proof
    [Prop 1, Prop 1 :|: Prop 1]
    ["Idempotence"]

idempotenceAnd :: a === a /\ a
idempotenceAnd = IsoProof $ TypedProof $ Proof
    [Prop 1, Prop 1 :&: Prop 1]
    ["Idempotence"]

-- Deduction rules

simplification :: a /\ b |- a
simplification = TypedProof $ Proof
    [Prop 1 :&: Prop 2, Prop 1]
    ["Simplification"]

addition :: a |- a \/ b
addition = TypedProof $ Proof
    [Prop 1, Prop 1 :|: Prop 2]
    ["Addition"]
