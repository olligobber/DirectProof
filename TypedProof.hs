{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

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
import Deduction

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
    IsoProof $ TypedProof $ P.liftLeft (getop @op) p

liftRight :: forall a b c op. BinOp op => a |~ b -> c `op` a |~ c `op` b
liftRight (IsoProof (TypedProof p)) =
    IsoProof $ TypedProof $ P.liftRight (getop @op) p

liftNot :: a |~ b -> Not a |~ Not b
liftNot (IsoProof (TypedProof p)) = IsoProof $ TypedProof $ P.mapWFF Not p

-- Equivalence rules (invertible)

deMorgans :: forall a b op1 op2. AlgOp op1 op2 =>
    Not (a `op1` b) |~ Not a `op2` Not b
deMorgans = IsoProof $ TypedProof $
    P.algebraicRule DeMorgans (getop @op1) (getop @op2)

commutation :: forall a b op op2. AlgOp op op2 =>
    a `op` b |~ b `op` a
commutation = IsoProof $ TypedProof $
    P.algebraicRule Commutation (getop @op) (getop @op2)

association :: forall a b c op op2. AlgOp op op2 =>
    a `op` (b `op` c) |~ (a `op` b) `op` c
association = IsoProof $ TypedProof $
    P.algebraicRule Association (getop @op) (getop @op2)

distribution :: forall a b c op1 op2. AlgOp op1 op2 =>
    a `op1` (b `op2` c) |~ (a `op1` b) `op2` (a `op1` c)
distribution = IsoProof $ TypedProof $
    P.algebraicRule Distribution (getop @op1) (getop @op2)

doubleNegation :: a |~ Not (Not a)
doubleNegation = IsoProof $ TypedProof $ P.equivalenceRule DoubleNegation

transposition :: a --> b |~ Not b --> Not a
transposition = IsoProof $ TypedProof $ P.equivalenceRule Transposition

defImplication :: a --> b |~ Not a \/ b
defImplication = IsoProof $ TypedProof $ P.equivalenceRule DefImplication

matEquivalence :: a <-> b |~ (a --> b) /\ (b --> a)
matEquivalence = IsoProof $ TypedProof $ P.equivalenceRule MatEquivalence

defEquivalence :: a <-> b |~ (a /\ b) \/ (Not a /\ Not b)
defEquivalence = IsoProof $ TypedProof $ P.equivalenceRule DefEquivalence

exportation :: (a /\ b) --> c |~ a --> (b --> c)
exportation = IsoProof $ TypedProof $ P.equivalenceRule Exportation

idempotence :: forall a op op2. AlgOp op op2 => a |~ a `op` a
idempotence = IsoProof $ TypedProof $
    P.algebraicRule Idempotence (getop @op) (getop @op2)

-- Deduction rules (directional)

modusPonens :: a |- b --> c -> a |- b -> a |- c
modusPonens (TypedProof p1) (TypedProof p2) =
    TypedProof $ P.complexRule ModusPonens p1 p2

modusTollens :: a |- b --> c -> a |- Not c -> a |- Not b
modusTollens (TypedProof p1) (TypedProof p2) =
    TypedProof $ P.complexRule ModusTollens p1 p2

hypotheticalS :: a |- b --> c -> a |- c --> d -> a |- b --> d
hypotheticalS (TypedProof p1) (TypedProof p2) =
    TypedProof $ P.complexRule HypotheticalS p1 p2

disjunctiveS :: a |- b \/ c -> a |- Not b -> a |- c
disjunctiveS (TypedProof p1) (TypedProof p2) =
    TypedProof $ P.complexRule DisjunctiveS p1 p2

constructiveD :: a |- (b --> c) /\ (d --> e) -> a |- b \/ d -> a |- c \/ e
constructiveD (TypedProof p1) (TypedProof p2) =
    TypedProof $ P.complexRule ConstructiveD p1 p2

destructiveD :: a |- (b --> c) /\ (d --> e) -> a |- Not c \/ Not e ->
    a |- Not b \/ Not d
destructiveD (TypedProof p1) (TypedProof p2) =
    TypedProof $ P.complexRule DestructiveD p1 p2

simplification :: a /\ b |- a
simplification = TypedProof $ P.simpleRule Simplification

conjunction :: a |- b -> a |- c -> a |- b /\ c
conjunction (TypedProof p1) (TypedProof p2) =
    TypedProof $ P.complexRule Conjunction p1 p2

addition :: a |- a \/ b
addition = TypedProof $ P.simpleRule Addition
