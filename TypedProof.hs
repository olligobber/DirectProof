{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}

module TypedProof (
    -- types and conversions
    type (|-)(), type (===)(), invert, toTyped, toPlain, render,
    -- lifts
    liftAndLeft, liftAndRight, liftOrLeft, liftOrRight, liftImpliesLeft,
    liftImpliesRight, liftEquivLeft, liftEquivRight, liftNot,
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
import qualified Data.Text as T
import Control.Category
import Data.String (fromString)

import Proof (Proof(Proof))
import qualified Proof as P
import ReLabel (reLabel)
import WFF (WFF(..))
import qualified WFF as W
import WFFType

-- Proof symbols
infix 2 |-
infix 2 ===

-- A one directional proof
newtype (|-) start end = TypedProof { toPlain :: Proof Integer}

instance Category (|-) where
    id = TypedProof mempty
    (TypedProof p2) . (TypedProof p1) = TypedProof $ p1 <> p2

render :: a |- b -> Text
render (TypedProof pf) = P.render (fromString . show) pf

-- Two directional proof
newtype (===) a b = IsoProof { toTyped :: a |- b }

instance Category (===) where
    id = IsoProof id
    IsoProof p2 . IsoProof p1 = IsoProof $ p2 . p1

invert :: a === b -> b === a
invert (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ P.invert p

-- Lift proofs as subformulas

liftAndLeft :: a === b -> a /\ c === b /\ c
liftAndLeft (IsoProof (TypedProof p)) = IsoProof $ TypedProof $
    P.liftLeft (:&:) p

liftAndRight :: a === b -> c /\ a === c /\ b
liftAndRight (IsoProof (TypedProof p)) = IsoProof $ TypedProof $
    P.liftRight (:&:) p

liftOrLeft :: a === b -> a \/ c === b \/ c
liftOrLeft (IsoProof (TypedProof p)) = IsoProof $ TypedProof $
    P.liftLeft (:|:) p

liftOrRight :: a === b -> c \/ a === c \/ b
liftOrRight (IsoProof (TypedProof p)) = IsoProof $ TypedProof $
    P.liftRight (:|:) p

liftImpliesLeft :: a === b -> a --> c === b --> c
liftImpliesLeft (IsoProof (TypedProof p)) = IsoProof $ TypedProof $
    P.liftLeft (:>:) p

liftImpliesRight :: a === b -> c --> a === c --> b
liftImpliesRight (IsoProof (TypedProof p)) = IsoProof $ TypedProof $
    P.liftRight (:>:) p

liftEquivLeft :: a === b -> a <-> c === b <-> c
liftEquivLeft (IsoProof (TypedProof p)) = IsoProof $ TypedProof $
    P.liftLeft (:=:) p

liftEquivRight :: a === b -> c <-> a === c <-> b
liftEquivRight (IsoProof (TypedProof p)) = IsoProof $ TypedProof $
    P.liftRight (:=:) p

liftNot :: a === b -> Not a === Not b
liftNot (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ P.mapWFF Not p

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
