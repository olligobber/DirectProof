{-# LANGUAGE OverloadedStrings #-}

module Deductions (
    Deduction,
    antes,
    apply,
    applyAny,
    SimpleDeduction,
    rules
) where

import Data.Text (Text)
import Data.Maybe (maybe)
import Data.Map.Lazy ((!))
import Control.Monad (replicateM)
import WFF (WFF(..))
import qualified WFF
import Mapping (Mapping(..))

class Deduction d where
    antes :: d -> Int -- Number of antecedents
    apply :: Eq c => d -> [WFF c] -> [WFF c] -- Apply the rule to the given antecedents to get a list of possible deductions, does not consider subsets of antecedents or reordering

instance (Deduction d, Deduction e) => Deduction (Either d e) where
    antes (Left deduction) = antes deduction
    antes (Right deduction) = antes deduction
    apply (Left deduction) = apply deduction
    apply (Right deduction) = apply deduction

-- Apply a rule to any subset of some formulas, returning the result and the list of lines used indexed by 0
applyAny :: (Eq c, Deduction d) => d -> [WFF c] -> [([Int], WFF c)]
applyAny deduction formulas = do
    (linenumbers, lineformulas) <- fmap unzip $ replicateM (antes deduction) $ zip [0..] formulas
    consequent <- apply deduction lineformulas
    return (linenumbers, consequent)

-- Simple proposition set
data Props = A | B | C | D | F | G | H
    deriving (Show, Eq, Ord)

-- Logical Sequent datatype
infix 4 :|-

data Sequent c = (:|-) [WFF c] (WFF c)

-- Get the infix constructor to render properly
instance Show c => Show (Sequent c) where
    showsPrec prec (antecedents :|- consequent) =
        showParen (prec>4) $ showsPrec 5 antecedents . showString " :|- " . showsPrec 5 consequent

instance Ord c => Deduction (Sequent c) where
    antes (antecedents :|- _) = length antecedents
    apply (antecedents :|- consequent) wffs
        | length antecedents /= length wffs = []
        | otherwise = case mconcat $ zipWith WFF.match antecedents wffs of
            Mapping Nothing -> []
            Mapping (Just mapping) -> [consequent >>= (mapping !)]

-- COMP2022 Sequents
sequents :: [(Text, Sequent Props)]
sequents = [
    ("MP", [Prop A :>: Prop B, Prop A] :|- Prop B),
    ("MT", [Prop A :>: Prop B, Not (Prop B)] :|- Not (Prop A)),
    ("HS", [Prop A :>: Prop B, Prop B :>: Prop C] :|- Prop A :>: Prop C),
    ("DS", [Prop A :|: Prop B, Not (Prop A)] :|- Prop B),
    ("CD", [(Prop A :>: Prop B) :&: (Prop C :>: Prop D), Prop A :|: Prop C] :|- Prop B :|: Prop D),
    ("DD", [(Prop A :>: Prop B) :&: (Prop C :>: Prop D), Not (Prop B) :|: Not (Prop D)] :|- Not (Prop A) :|: Not (Prop C)),
    ("Simp", [Prop A :&: Prop B] :|- Prop A),
    ("Conj", [Prop A, Prop B] :|- Prop A :&: Prop B)
    ]

-- Logical Equivalence datatype
infix 4 :==

data Equivalence c = (:==) (WFF c) (WFF c)

-- Get the infix constructor to render properly
instance Show c => Show (Equivalence c) where
    showsPrec prec (wff1 :== wff2) =
        showParen (prec>4) $ showsPrec 5 wff1 . showString " :== " . showsPrec 5 wff2

instance Ord c => Deduction (Equivalence c) where
    antes _ = 1
    apply (left :== right) [wff] = apply' left right ++ apply' right left where
        apply' antecedent consequent = do
            (mapping, matched) <- WFF.allMatch antecedent wff
            return $ matched >>= maybe (consequent >>= (mapping !)) Prop
    apply _ _ = []

-- COMP2022 Equivalences
equivalences :: [(Text, Equivalence Props)]
equivalences = [
    ("DeM", Not (Prop F :&: Prop G) :== Not (Prop F) :|: Not (Prop G)),
    ("DeM", Not (Prop F :|: Prop G) :== Not (Prop F) :&: Not (Prop G)),
    ("Comm", Prop F :|: Prop G :== Prop G :|: Prop F),
    ("Comm", Prop F :&: Prop G :== Prop G :&: Prop F),
    ("Assoc", Prop F :|: (Prop G :|: Prop H) :== (Prop F :|: Prop G) :|: Prop H),
    ("Assoc", Prop F :&: (Prop G :&: Prop H) :== (Prop F :&: Prop G) :&: Prop H),
    ("Dist", Prop F :&: (Prop G :|: Prop H) :== (Prop F :&: Prop G) :|: (Prop F :&: Prop H)),
    ("Dist", Prop F :|: (Prop G :&: Prop H) :== (Prop F :|: Prop G) :&: (Prop F :|: Prop H)),
    ("DN", Prop F :== Not (Not (Prop F))),
    ("Trans", Prop F :>: Prop G :== Not (Prop G) :>: Not (Prop F)),
    ("DefI", Prop F :>: Prop G :== Not (Prop F) :|: Prop G),
    ("Equiv", Prop F :=: Prop G :== (Prop F :>: Prop G) :&: (Prop G :>: Prop F)),
    ("DefE", Prop F :=: Prop G :== (Prop F :&: Prop G) :|: (Not (Prop F) :&: Not (Prop G))),
    ("Exp", (Prop F :&: Prop G) :>: Prop H :== Prop F :>: (Prop G :>: Prop H)),
    ("Idem", Prop F :== Prop F :|: Prop F),
    ("Idem", Prop F :== Prop F :&: Prop F)
    ]

-- COMP2022 Rules
type SimpleDeduction = Either (Sequent Props) (Equivalence Props)

rules :: [(Text, SimpleDeduction)]
rules = (fmap Left <$> sequents) ++ (fmap Right <$> equivalences)
