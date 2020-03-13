{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Deduction (
    -- Rules
    AlgebraicRule(..), EquivRule(..), SimpleRule(..), ComplexRule(..),
    -- Rule parts
    makeEquivs, getEquivs, getImplies, getParts,
    -- Rule verification
    verifyAlg, verifyEquivs, verifySimple, verifyComplex,
    -- Deductions
    Deduction(..), changeRef, renderDeduction, invertible
) where

import Data.Text (Text)
import Data.String (fromString)
import Data.List (sort)
import Data.Function (on)

import WFF (WFF(..), BinaryOperator, matchSub)
import Mapping (Mapping(..))
import Render (Renderable(..))

-- Helpers for verification functions

flipPair :: (a, b) -> (b, a)
flipPair = uncurry $ flip (,)

verifyTwo :: (Ord x, Eq y) => (WFF x, WFF x) -> WFF y -> WFF y -> Bool
verifyTwo (left1, right1) left2 right2 =
    matchSub (left1 :>: right1) (left2 :>: right2) /= Mapping Nothing

verifySub :: (Ord x, Eq y) => (WFF x, WFF x) -> WFF y -> WFF y -> Bool
verifySub format w1@(left1 :&: right1) w2@(left2 :&: right2) = any id
    [ left1 == left2 && verifySub format right1 right2
    , right1 == right2 && verifySub format left1 left2
    , verifyTwo format w1 w2
    ]
verifySub format w1@(left1 :|: right1) w2@(left2 :|: right2) = any id
    [ left1 == left2 && verifySub format right1 right2
    , right1 == right2 && verifySub format left1 left2
    , verifyTwo format w1 w2
    ]
verifySub format w1@(left1 :>: right1) w2@(left2 :>: right2) = any id
    [ left1 == left2 && verifySub format right1 right2
    , right1 == right2 && verifySub format left1 left2
    , verifyTwo format w1 w2
    ]
verifySub format w1@(left1 :=: right1) w2@(left2 :=: right2) = any id
    [ left1 == left2 && verifySub format right1 right2
    , right1 == right2 && verifySub format left1 left2
    , verifyTwo format w1 w2
    ]
verifySub format w1@(Not s1) w2@(Not s2) = any id
    [ verifySub format s1 s2, verifyTwo format w1 w2 ]
verifySub format w1 w2 = verifyTwo format w1 w2

verifyThree :: (Ord x, Eq y) => (WFF x, WFF x, WFF x) ->
    WFF y -> WFF y -> WFF y -> Bool
verifyThree (left1, right1, out1) left2 right2 out2 = Mapping Nothing /=
    matchSub ((left1 :&: right1) :>: out1) ((left2 :&: right2) :>: out2)

-- Rules that can be applied to Or and And

data AlgebraicRule
    = DeMorgans
    | Commutation
    | Association
    | Distribution
    | Idempotence
    deriving (Show, Eq)

instance Renderable AlgebraicRule where
    render = fromString . show

makeEquivs :: AlgebraicRule -> BinaryOperator -> BinaryOperator ->
    (WFF Integer, WFF Integer)
makeEquivs DeMorgans (&&&) (|||) =
    (Not (Prop 1 &&& Prop 2), Not (Prop 1) ||| Not (Prop 2))
makeEquivs Commutation (&&&) _ = (Prop 1 &&& Prop 2, Prop 2 &&& Prop 1)
makeEquivs Association (&&&) _ =
    (Prop 1 &&& (Prop 2 &&& Prop 3), (Prop 1 &&& Prop 2) &&& Prop 3)
makeEquivs Distribution (&&&) (|||) = (Prop 1 &&& (Prop 2 ||| Prop 3),
    (Prop 1 &&& Prop 2) ||| (Prop 1 &&& Prop 3))
makeEquivs Idempotence (&&&) _ = (Prop 1, Prop 1 &&& Prop 1)

verifyAlg :: Eq x => AlgebraicRule -> WFF x -> WFF x -> Bool
verifyAlg rule w1 w2 = any (\p -> verifySub p w1 w2)
    [ makeEquivs rule (:&:) (:|:)
    , flipPair $ makeEquivs rule (:&:) (:|:)
    , makeEquivs rule (:|:) (:&:)
    , flipPair $ makeEquivs rule (:|:) (:&:)
    ]

-- Reversible rules

data EquivRule
    = DoubleNegation
    | Transposition
    | DefImplication
    | MatEquivalence
    | DefEquivalence
    | Exportation
    deriving (Show, Eq)

instance Renderable EquivRule where
    render DoubleNegation = "Double Negation"
    render DefImplication = "Definition of Implication"
    render MatEquivalence = "Material Equivalence"
    render DefEquivalence = "Definition of Equivalence"
    render r = fromString $ show r

getEquivs :: EquivRule -> (WFF Integer, WFF Integer)
getEquivs DoubleNegation = (Prop 1, Not $ Not $ Prop 1)
getEquivs Transposition = (Prop 1 :>: Prop 2, Not (Prop 2) :>: Not (Prop 1))
getEquivs DefImplication = (Prop 1 :>: Prop 2, Not (Prop 1) :|: Prop 2)
getEquivs MatEquivalence =
    (Prop 1 :=: Prop 2, (Prop 1 :>: Prop 2) :&: (Prop 2 :>: Prop 1))
getEquivs DefEquivalence = (Prop 1 :=: Prop 2,
    (Prop 1 :&: Prop 2) :|: (Not (Prop 1) :&: Not (Prop 2)))
getEquivs Exportation =
    ((Prop 1 :&: Prop 2) :>: Prop 3, Prop 1 :>: (Prop 2 :>: Prop 3))

verifyEquivs :: Eq x => EquivRule -> WFF x -> WFF x -> Bool
verifyEquivs rule w1 w2 = any (\p -> verifySub p w1 w2)
    [getEquivs rule, flipPair $ getEquivs rule]

-- Rules with one input and one output

data SimpleRule = Simplification | Addition deriving (Show, Eq)

instance Renderable SimpleRule where
    render = fromString . show

getImplies :: SimpleRule -> (WFF Integer, WFF Integer)
getImplies Simplification = (Prop 1 :&: Prop 2, Prop 1)
getImplies Addition = (Prop 1, Prop 1 :|: Prop 2)

verifySimple :: Eq x => SimpleRule -> WFF x -> WFF x -> Bool
verifySimple rule = verifyTwo $ getImplies rule

-- Rules with multiple inputs

data ComplexRule
    = ModusPonens
    | ModusTollens
    | HypotheticalS
    | DisjunctiveS
    | ConstructiveD
    | DestructiveD
    | Conjunction
    deriving (Show, Eq)

instance Renderable ComplexRule where
    render ModusPonens = "Modus Ponens"
    render ModusTollens = "Modus Tollens"
    render HypotheticalS = "Hypothetical Syllogism"
    render DisjunctiveS = "Disjunctive Syllogism"
    render ConstructiveD = "Constructive Dilemma"
    render DestructiveD = "Destructive Dilemma"
    render Conjunction = "Conjunction"

getParts :: ComplexRule -> (WFF Integer, WFF Integer, WFF Integer)
getParts ModusPonens = (Prop 1 :>: Prop 2, Prop 1, Prop 2)
getParts ModusTollens = (Prop 1 :>: Prop 2, Not $ Prop 1, Not $ Prop 2)
getParts HypotheticalS =
    (Prop 1 :>: Prop 2, Prop 2 :>: Prop 3, Prop 1 :>: Prop 3)
getParts DisjunctiveS = (Prop 1 :|: Prop 2, Not $ Prop 1, Prop 2)
getParts ConstructiveD = ((Prop 1 :>: Prop 2) :&: (Prop 3 :>: Prop 4),
    Prop 1 :|: Prop 3, Prop 2 :|: Prop 4)
getParts DestructiveD = ((Prop 1 :>: Prop 2) :&: (Prop 3 :>: Prop 4),
    Not (Prop 2) :|: Not (Prop 4), Not (Prop 1) :|: Not (Prop 3))
getParts Conjunction = (Prop 1, Prop 2, Prop 1 :&: Prop 2)

verifyComplex :: Eq x => ComplexRule -> WFF x -> WFF x -> WFF x -> Bool
verifyComplex rule = verifyThree $ getParts rule

{-
    Deduction in a proof.
    Integers store references to previous lines, e.g. 1 is line before.
-}
data Deduction
    = Assumption
    | Algebraic AlgebraicRule Integer
    | Equiv EquivRule Integer
    | Simple SimpleRule Integer
    | Complex ComplexRule Integer Integer
    deriving (Show, Eq)

changeIf :: (a -> Bool) -> (a -> a) -> a -> a
changeIf c f x
    | c x = f x
    | otherwise = x

-- Increase all references to a particular line by a certain offset
changeRef :: Integer -> Deduction -> Integer -> Deduction
changeRef _ Assumption _ = Assumption
changeRef offset (Algebraic r i) change =
    Algebraic r $ changeIf (==change) (+offset) i
changeRef offset (Equiv r i) change =
    Equiv r $ changeIf (==change) (+offset) i
changeRef offset (Simple r i) change =
    Simple r $ changeIf (==change) (+offset) i
changeRef offset (Complex r i j) change =
    (Complex r `on` changeIf (==change) (+offset)) i j

-- Given the line number, render a deduction
renderDeduction :: Deduction -> Integer -> Text
renderDeduction Assumption _ = "Assumption"
renderDeduction (Algebraic r i) l = render r <> " " <> render (l-i)
renderDeduction (Equiv r i) l = render r <> " " <> render (l-i)
renderDeduction (Simple r i) l = render r <> " " <> render (l-i)
renderDeduction (Complex r i j) l =
    render r <> " " <> render i1 <> "," <> render j1 where
        [i1,j1] = sort [l-i, l-j]

-- Equivalence rules with reference to the previous line are reversible
invertible :: Deduction -> Bool
invertible (Algebraic _ 1) = True
invertible (Equiv _ 1) = True
invertible _ = False
