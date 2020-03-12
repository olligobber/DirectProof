{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TypedProof (
    -- types and conversions
    type (|-)(), type (|~)(), invert, toTyped, toPlain, render,
    -- lifts
    liftLeft, liftRight, liftNot,
    -- equivalence rules
    deMorgans, commutation, association, distribution, doubleNegation,
    transposition, defImplication, matEquivalence, defEquivalence, exportation,
    idempotence,
    -- deduction rules
    modusPonens, modusTollens, hypotheticalS, disjunctiveS, constructiveD,
    destructiveD, simplification, conjunction, addition
) where

import Prelude hiding (id, (.)) -- Control.Category redefines these
import Control.Category

import Proof (Proof)
import qualified Proof as P
import WFF (WFF(..))
import WFFType
import Render (Renderable(..))

-- A one directional proof
infix 2 |-
newtype (|-) start end = TypedProof { toPlain :: Proof Integer}

{-
    Allow proof composition only when the end of one matches the start of the
    next, using (>>>) :: a |- b -> b |- c -> a |- c
-}
instance Category (|-) where
    id = TypedProof mempty
    (TypedProof p2) . (TypedProof p1) = TypedProof $ p1 <> p2

-- Allow pretty rendering of proofs
instance Renderable (a |- b) where
    render (TypedProof pf) = render $ ("p_" <>) . show <$> pf

-- Invertible proofs
infix 2 |~
newtype (|~) a b = IsoProof { toTyped :: a |- b }

-- Allow proof composition similar to |-
instance Category (|~) where
    id = IsoProof id
    IsoProof p2 . IsoProof p1 = IsoProof $ p2 . p1

-- Allow pretty rendering of proofs
instance Renderable (a |~ b) where
    render (IsoProof pf) = render pf

invert :: a |~ b -> b |~ a
invert (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ P.invert p

-- Lift invertible proofs by application to subformulas

liftLeft :: forall a b c op. BinOp op => a |~ b -> a `op` c |~ b `op` c
liftLeft (IsoProof (TypedProof p)) =
    IsoProof $ TypedProof $ P.liftLeft (extract (getop :: op () ())) p

liftRight :: forall a b c op. BinOp op => a |~ b -> c `op` a |~ c `op` b
liftRight (IsoProof (TypedProof p)) =
    IsoProof $ TypedProof $ P.liftRight (extract (getop :: op () ())) p

liftNot :: a |~ b -> Not a |~ Not b
liftNot (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ P.mapWFF Not p

-- Equivalence rules (invertible)

deMorgans :: forall a b op1 op2. AlgOp op1 op2 =>
    Not (a `op1` b) |~ Not a `op2` Not b
deMorgans = IsoProof $ TypedProof $ P.simpleRule
    (Not (Prop 1 *& Prop 2))
    (Not (Prop 1) *+ Not (Prop 2))
    "De Morgan's"
    where
        (*&) = extract (getop :: op1 () ())
        (*+) = extract (getop :: op2 () ())

commutation :: forall a b op op2. AlgOp op op2 =>
    a `op` b |~ b `op` a
commutation = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 *& Prop 2)
    (Prop 2 *& Prop 1)
    "Commutation"
    where
        (*&) = extract (getop :: op () ())

association :: forall a b c op op2. AlgOp op op2 =>
    a `op` (b `op` c) |~ (a `op` b) `op` c
association = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 *& (Prop 2 *& Prop 3))
    ((Prop 1 *& Prop 2) *& Prop 3)
    "Association"
    where
        (*&) = extract (getop :: op () ())

distribution :: forall a b c op1 op2. AlgOp op1 op2 =>
    a `op1` (b `op2` c) |~ (a `op1` b) `op2` (a `op1` c)
distribution = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 *& (Prop 2 *+ Prop 3))
    ((Prop 1 *& Prop 2) *+ (Prop 1 *& Prop 3))
    "Distribution"
    where
        (*&) = extract (getop :: op1 () ())
        (*+) = extract (getop :: op2 () ())

doubleNegation :: a |~ Not (Not a)
doubleNegation = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1)
    (Not $ Not $ Prop 1)
    "Double Negation"

transposition :: a --> b |~ Not b --> Not a
transposition = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 :>: Prop 2)
    (Not (Prop 2) :>: Not (Prop 1))
    "Transposition"

defImplication :: a --> b |~ Not a \/ b
defImplication = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 :>: Prop 2)
    (Not (Prop 1) :|: Prop 2)
    "Definition of Implication"

matEquivalence :: a <-> b |~ (a --> b) /\ (b --> a)
matEquivalence = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 :=: Prop 2)
    ((Prop 1 :>: Prop 2) :&: (Prop 2 :>: Prop 1))
    "Material Equivalence"

defEquivalence :: a <-> b |~ (a /\ b) \/ (Not a /\ Not b)
defEquivalence = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 :=: Prop 2)
    ((Prop 1 :&: Prop 2) :|: (Not (Prop 1) :&: Not (Prop 2)))
    "Definition of Equivalence"

exportation :: (a /\ b) --> c |~ a --> (b --> c)
exportation = IsoProof $ TypedProof $ P.simpleRule
    ((Prop 1 :&: Prop 2) :>: Prop 3)
    (Prop 1 :>: (Prop 2 :>: Prop 3))
    "Exportation"

idempotence :: forall a op op2. AlgOp op op2 => a |~ a `op` a
idempotence = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1)
    (extract (getop :: op () ()) (Prop 1) (Prop 1))
    "Idempotence"

-- Deduction rules (directional)

modusPonens :: a |- b --> c -> a |- b -> a |- c
modusPonens (TypedProof p1) (TypedProof p2) = TypedProof $ P.complexRule
    (Prop 1 :>: Prop 2)
    (Prop 1)
    (Prop 2)
    "Modus Ponens"
    p1
    p2

modusTollens :: a |- b --> c -> a |- Not c -> a |- Not b
modusTollens (TypedProof p1) (TypedProof p2) = TypedProof $ P.complexRule
    (Prop 1 :>: Prop 2)
    (Not $ Prop 2)
    (Not $ Prop 1)
    "Modus Tollens"
    p1
    p2

hypotheticalS :: a |- b --> c -> a |- c --> d -> a |- b --> d
hypotheticalS (TypedProof p1) (TypedProof p2) = TypedProof $ P.complexRule
    (Prop 1 :>: Prop 2)
    (Prop 2 :>: Prop 3)
    (Prop 1 :>: Prop 3)
    "Hypothetical Syllogism"
    p1
    p2

disjunctiveS :: a |- b \/ c -> a |- Not b -> a |- c
disjunctiveS (TypedProof p1) (TypedProof p2) = TypedProof $ P.complexRule
    (Prop 1 :|: Prop 2)
    (Not $ Prop 1)
    (Prop 2)
    "Disjunctive Syllogism"
    p1
    p2

constructiveD :: a |- (b --> c) /\ (d --> e) -> a |- b \/ d -> a |- c \/ e
constructiveD (TypedProof p1) (TypedProof p2) = TypedProof $ P.complexRule
    ((Prop 1 :>: Prop 2) :&: (Prop 3 :>: Prop 4))
    (Prop 1 :|: Prop 3)
    (Prop 2 :|: Prop 4)
    "Constructive Dilemma"
    p1
    p2

destructiveD :: a |- (b --> c) /\ (d --> e) -> a |- Not c \/ Not e ->
    a |- Not b \/ Not d
destructiveD (TypedProof p1) (TypedProof p2) = TypedProof $ P.complexRule
    ((Prop 1 :>: Prop 2) :&: (Prop 3 :>: Prop 4))
    (Not (Prop 2) :|: Not (Prop 4))
    (Not (Prop 1) :|: Not (Prop 3))
    "Destructive Dilemma"
    p1
    p2

simplification :: a /\ b |- a
simplification = TypedProof $ P.simpleRule
    (Prop 1 :&: Prop 2)
    (Prop 1)
    "Simplification"

conjunction :: a |- b -> a |- c -> a |- b /\ c
conjunction (TypedProof p1) (TypedProof p2) = TypedProof $ P.complexRule
    (Prop 1)
    (Prop 2)
    (Prop 1 :&: Prop 2)
    "Conjunction"
    p1
    p2

addition :: a |- a \/ b
addition = TypedProof $ P.simpleRule
    (Prop 1)
    (Prop 1 :|: Prop 2)
    "Addition"
