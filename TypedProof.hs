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
    deMorgans1, deMorgans2, commutationOr, commutationAnd, associationOr,
    associationAnd, distribution1, distribution2, doubleNegation,
    transposition, defImplication, matEquivalence, defEquivalence, exportation,
    idempotenceOr, idempotenceAnd,
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

-- Proof symbols
infix 2 |-
infix 2 |~

-- A one directional proof
newtype (|-) start end = TypedProof { toPlain :: Proof Integer}

instance Category (|-) where
    id = TypedProof mempty
    (TypedProof p2) . (TypedProof p1) = TypedProof $ p1 <> p2

instance Renderable (a |- b) where
    render (TypedProof pf) = render $ ("p_" <>) . show <$> pf

-- Two directional proof
newtype (|~) a b = IsoProof { toTyped :: a |- b }

instance Category (|~) where
    id = IsoProof id
    IsoProof p2 . IsoProof p1 = IsoProof $ p2 . p1

instance Renderable (a |~ b) where
    render (IsoProof pf) = render pf

invert :: a |~ b -> b |~ a
invert (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ P.invert p

-- Lift proofs as subformulas

liftLeft :: forall a b c op. BinOp op => a |~ b -> op a c |~ op b c
liftLeft (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ P.liftLeft
    (extract (getop :: op () ())) p

liftRight :: forall a b c op. BinOp op => a |~ b -> op c a |~ op c b
liftRight (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ P.liftRight
    (extract (getop :: op () ())) p

liftNot :: a |~ b -> Not a |~ Not b
liftNot (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ P.mapWFF Not p

-- Equivalence rules

deMorgans1 :: Not (a /\ b) |~ Not a \/ Not b
deMorgans1 = IsoProof $ TypedProof $ P.simpleRule
    (Not $ Prop 1 :&: Prop 2)
    (Not (Prop 1) :|: Not (Prop 2))
    "De Morgan's"

deMorgans2 :: Not (a \/ b) |~ Not a /\ Not b
deMorgans2 = IsoProof $ TypedProof $ P.simpleRule
    (Not $ Prop 1 :|: Prop 2)
    (Not (Prop 1) :&: Not (Prop 2))
    "De Morgan's"

commutationOr :: a \/ b |~ b \/ a
commutationOr = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 :|: Prop 2)
    (Prop 2 :|: Prop 1)
    "Commutation"

commutationAnd :: a /\ b |~ b /\ a
commutationAnd = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 :&: Prop 2)
    (Prop 2 :&: Prop 1)
    "Commutation"

associationOr :: a \/ (b \/ c) |~ (a \/ b) \/ c
associationOr = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 :|: (Prop 2 :|: Prop 3))
    ((Prop 1 :|: Prop 2) :|: Prop 3)
    "Association"

associationAnd :: a /\ (b /\ c) |~ (a /\ b) /\ c
associationAnd = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 :&: (Prop 2 :&: Prop 3))
    ((Prop 1 :&: Prop 2) :&: Prop 3)
    "Association"

distribution1 :: a /\ (b \/ c) |~ (a /\ b) \/ (a /\ c)
distribution1 = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 :&: (Prop 2 :|: Prop 3))
    ((Prop 1 :&: Prop 2) :|: (Prop 1 :&: Prop 3))
    "Distribution"

distribution2 :: a \/ (b /\ c) |~ (a \/ b) /\ (a \/ c)
distribution2 = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1 :|: (Prop 2 :&: Prop 3))
    ((Prop 1 :|: Prop 2) :&: (Prop 1 :|: Prop 3))
    "Distribution"

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

idempotenceOr :: a |~ a \/ a
idempotenceOr = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1)
    (Prop 1 :|: Prop 1)
    "Idempotence"

idempotenceAnd :: a |~ a /\ a
idempotenceAnd = IsoProof $ TypedProof $ P.simpleRule
    (Prop 1)
    (Prop 1 :&: Prop 1)
    "Idempotence"

-- Deduction rules

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
