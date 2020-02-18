{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

import Prelude hiding (id, (.))
import Data.Text (Text)
import qualified Data.Text as T
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import Control.Category
import Mapping (BiMapping(..))
import WFF (WFF(..))
import qualified WFF as W
import WFFType

data TypedProof start end = TypedProof {
    formulas :: [WFF Integer],
    reasons :: [Text]
}

reLabel :: Ord x => [WFF x] -> [WFF Integer]
reLabel = W.reLabelAll [1..]

type (|-) = TypedProof

instance Category TypedProof where
    id = TypedProof [Prop 1] []
    p2 . p1 = case W.match p1end p2start of
        (BiMapping (Just (f,b))) -> TypedProof
            ( reLabel $
                (W.applyMapLeft f <$> formulas p1) ++ tail
                (W.applyMapRight b <$> formulas p2) )
            ( reasons p1 ++ reasons p2 )
        _ -> error $ unlines
            [ "Failed to compose proofs, since the following formulas did not match:"
            , "    " ++ show p1end
            , "    " ++ show p2start
            ]
        where
            p1end = last $ formulas p1
            p2start = head $ formulas p2

newtype IsoProof a b = IsoProof { toTyped :: a |- b }

type (===) = IsoProof

instance Category IsoProof where
    id = IsoProof id
    IsoProof p2 . IsoProof p1 = IsoProof $ p2 . p1

invert :: a === b -> b === a
invert (IsoProof p) = IsoProof $ TypedProof
    (reverse $ formulas p)
    (reverse $ reasons p)

liftAnd1 :: a === b -> (a /\ c) === (b /\ c)
liftAnd1 (IsoProof p) = IsoProof $ TypedProof
    (reLabel ((:&: Prop Nothing) . fmap Just <$> formulas p))
    (reasons p)

liftAnd2 :: a === b -> (c /\ a) === (c /\ b)
liftAnd2 (IsoProof p) = IsoProof $ TypedProof
    (reLabel ((Prop Nothing :&:) . fmap Just <$> formulas p))
    (reasons p)

liftOr1 :: a === b -> (a \/ c) === (b \/ c)
liftOr1 (IsoProof p) = IsoProof $ TypedProof
    (reLabel ((:|: Prop Nothing) . fmap Just <$> formulas p))
    (reasons p)

liftOr2 :: a === b -> (c \/ a) === (c \/ b)
liftOr2 (IsoProof p) = IsoProof $ TypedProof
    (reLabel ((Prop Nothing :|:) . fmap Just <$> formulas p))
    (reasons p)

liftImplies1 :: a === b -> (a --> c) === (b --> c)
liftImplies1 (IsoProof p) = IsoProof $ TypedProof
    (reLabel ((:>: Prop Nothing) . fmap Just <$> formulas p))
    (reasons p)

liftImplies2 :: a === b -> (c --> a) === (c --> b)
liftImplies2 (IsoProof p) = IsoProof $ TypedProof
    (reLabel ((Prop Nothing :>:) . fmap Just <$> formulas p))
    (reasons p)

liftEquiv1 :: a === b -> (a <-> c) === (b <-> c)
liftEquiv1 (IsoProof p) = IsoProof $ TypedProof
    (reLabel ((:=: Prop Nothing) . fmap Just <$> formulas p))
    (reasons p)

liftEquiv2 :: a === b -> (c <-> a) === (c <-> b)
liftEquiv2 (IsoProof p) = IsoProof $ TypedProof
    (reLabel ((Prop Nothing :=:) . fmap Just <$> formulas p))
    (reasons p)

liftNot :: a === b -> Not a === Not b
liftNot (IsoProof p) = IsoProof $ TypedProof
    (Not <$> formulas p)
    (reasons p)

deMorgans1 :: (Not (a /\ b)) === (Not a \/ Not b)
deMorgans1 = IsoProof $ TypedProof
    [Not $ Prop 1 :&: Prop 2, Not (Prop 1) :|: Not (Prop 2)]
    ["De Morgan's"]

deMorgans2 :: (Not (a \/ b)) === (Not a /\ Not b)
deMorgans2 = IsoProof $ TypedProof
    [Not $ Prop 1 :|: Prop 2, Not (Prop 1) :&: Not (Prop 2)]
    ["De Morgan's"]

commutationOr :: (a \/ b) === (b \/ a)
commutationOr = IsoProof $ TypedProof
    [Prop 1 :|: Prop 2, Prop 2 :|: Prop 1]
    ["Commutation"]

commutationAnd :: (a /\ b) === (b /\ a)
commutationAnd = IsoProof $ TypedProof
    [Prop 1 :&: Prop 2, Prop 2 :&: Prop 1]
    ["Commutation"]

associationOr :: (a \/ (b \/ c)) === ((a \/ b) \/ c)
associationOr = IsoProof $ TypedProof
    [Prop 1 :|: (Prop 2 :|: Prop 3), (Prop 1 :|: Prop 2) :|: Prop 3]
    ["Association"]

associationAnd :: (a /\ (b /\ c)) === ((a /\ b) /\ c)
associationAnd = IsoProof $ TypedProof
    [Prop 1 :&: (Prop 2 :&: Prop 3), (Prop 1 :&: Prop 2) :&: Prop 3]
    ["Association"]

distribution1 :: (a /\ (b \/ c)) === ((a /\ b) \/ (a /\ c))
distribution1 = IsoProof $ TypedProof
    [Prop 1 :&: (Prop 2 :|: Prop 3), (Prop 1 :&: Prop 2) :|: (Prop 1 :&: Prop 3)]
    ["Distribution"]

distribution2 :: (a \/ (b /\ c)) === ((a \/ b) /\ (a \/ c))
distribution2 = IsoProof $ TypedProof
    [Prop 1 :|: (Prop 2 :&: Prop 3), (Prop 1 :|: Prop 2) :&: (Prop 1 :|: Prop 3)]
    ["Distribution"]

doubleNegation :: a === Not (Not a)
doubleNegation = IsoProof $ TypedProof
    [Prop 1, Not $ Not $ Prop 1]
    ["Double Negation"]

transposition :: (a --> b) === (Not b --> Not a)
transposition = IsoProof $ TypedProof
    [Prop 1 :>: Prop 2, Not (Prop 2) :>: Not (Prop 1)]
    ["Transposition"]

defImplication :: (a --> b) === (Not a \/ b)
defImplication = IsoProof $ TypedProof
    [Prop 1 :>: Prop 2, Not (Prop 1) :|: Prop 2]
    ["Definition of Implication"]

matEquivalence :: (a <-> b) === ((a --> b) /\ (b --> a))
matEquivalence = IsoProof $ TypedProof
    [Prop 1 :=: Prop 2, (Prop 1 :>: Prop 2) :&: (Prop 2 :>: Prop 1)]
    ["Material Equivalence"]

defEquivalence :: (a <-> b) === ((a /\ b) \/ (Not a /\ Not b))
defEquivalence = IsoProof $ TypedProof
    [Prop 1 :=: Prop 2, (Prop 1 :&: Prop 2) :|: (Not (Prop 1) :&: Not (Prop 2))]
    ["Definition of Equivalence"]

exportation :: ((a /\ b) --> c) === (a --> (b --> c))
exportation = IsoProof $ TypedProof
    [(Prop 1 :&: Prop 2) :>: Prop 3, Prop 1 :>: (Prop 2 :>: Prop 3)]
    ["Exportation"]

idempotenceOr :: a === (a \/ a)
idempotenceOr = IsoProof $ TypedProof
    [Prop 1, Prop 1 :|: Prop 1]
    ["Idempotence"]

idempotenceAnd :: a === (a /\ a)
idempotenceAnd = IsoProof $ TypedProof
    [Prop 1, Prop 1 :&: Prop 1]
    ["Idempotence"]

simplification :: (a /\ b) |- a
simplification = TypedProof
    [Prop 1 :&: Prop 2, Prop 1]
    ["Simplification"]

addition :: a |- (a \/ b)
addition = TypedProof
    [Prop 1, Prop 1 :|: Prop 2]
    ["Addition"]
