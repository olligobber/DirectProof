{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

import Prelude hiding (id, (.))
import Data.Text (Text)
import qualified Data.Text as T
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import Control.Category
import WFF (WFF(..), match, Mapping(..))
import WFFType

type Bound = Int

data TypedProof start end = TypedProof {
    formulas :: [WFF Int],
    reasons :: [Text],
    bound :: Bound
}

type (|-) = TypedProof

-- Given propositions in the first bound that map to formulas in the second,
-- finds the required size for the combined range
newBound :: Map Int (WFF Int) -> Bound -> Bound -> Bound
newBound mapping first second = first + second - M.size mapping

-- Given propositions in the first range that map to formulas in the second,
-- map propositions in the first range to formulas in the combined range
mapInts :: Map Int (WFF Int) -> Bound -> Bound -> Int -> WFF Int
mapInts mapping first second x = case M.lookup x mapping of
    Just wff -> wff
    Nothing -> Prop $ second + length (filter (`M.notMember` mapping) [1..x])

instance Category TypedProof where
    id = TypedProof [Prop 1] [] 1
    p2 . p1 = case (match p1end p2start, match p2start p1end) of
        (Mapping (Just m), _) -> TypedProof
            ( fmap (>>= mapInts m (bound p1) (bound p2)) (formulas p1)
                ++ tail (formulas p2) )
            ( reasons p1 ++ reasons p2 )
            ( newBound m (bound p1) (bound p2) )
        (_, Mapping (Just m)) -> TypedProof
            ( init (formulas p1) ++
                fmap (>>= mapInts m (bound p2) (bound p1)) (formulas p2) )
            ( reasons p1 ++ reasons p2 )
            ( newBound m (bound p2) (bound p1) )
        _ -> error $ unwords
            [ "Failed to compose, as formulas"
            , show p1end
            , "and"
            , show p2start
            , "did not match"
            ]
        where
            p1end = last (formulas p1)
            p2start = head (formulas p2)

newtype IsoProof a b = IsoProof { toTyped :: a |- b }

type (===) = IsoProof

instance Category IsoProof where
    id = IsoProof id
    IsoProof p2 . IsoProof p1 = IsoProof $ p2 . p1

invert :: a === b -> b === a
invert (IsoProof p) = IsoProof $ TypedProof
    (reverse $ formulas p)
    (reverse $ reasons p)
    (bound p)

deMorgans1 :: (Not (a /\ b)) === (Not a \/ Not b)
deMorgans1 = IsoProof $ TypedProof
    [Not $ Prop 1 :&: Prop 2, Not (Prop 1) :|: Not (Prop 2)]
    ["De Morgan's"]
    2

deMorgans2 :: (Not (a \/ b)) === (Not a /\ Not b)
deMorgans2 = IsoProof $ TypedProof
    [Not $ Prop 1 :|: Prop 2, Not (Prop 1) :&: Not (Prop 2)]
    ["De Morgan's"]
    2

commutationOr :: (a \/ b) === (b \/ a)
commutationOr = IsoProof $ TypedProof
    [Prop 1 :|: Prop 2, Prop 2 :|: Prop 1]
    ["Commutation"]
    2

commutationAnd :: (a /\ b) === (b /\ a)
commutationAnd = IsoProof $ TypedProof
    [Prop 1 :&: Prop 2, Prop 2 :&: Prop 1]
    ["Commutation"]
    2

associationOr :: (a \/ (b \/ c)) === ((a \/ b) \/ c)
associationOr = IsoProof $ TypedProof
    [Prop 1 :|: (Prop 2 :|: Prop 3), (Prop 1 :|: Prop 2) :|: Prop 3]
    ["Association"]
    3

associationAnd :: (a /\ (b /\ c)) === ((a /\ b) /\ c)
associationAnd = IsoProof $ TypedProof
    [Prop 1 :&: (Prop 2 :&: Prop 3), (Prop 1 :&: Prop 2) :&: Prop 3]
    ["Association"]
    3

distribution1 :: (a /\ (b \/ c)) === ((a /\ b) \/ (a /\ c))
distribution1 = IsoProof $ TypedProof
    [Prop 1 :&: (Prop 2 :|: Prop 3), (Prop 1 :&: Prop 2) :|: (Prop 1 :&: Prop 3)]
    ["Distribution"]
    3

distribution2 :: (a \/ (b /\ c)) === ((a \/ b) /\ (a \/ c))
distribution2 = IsoProof $ TypedProof
    [Prop 1 :|: (Prop 2 :&: Prop 3), (Prop 1 :|: Prop 2) :&: (Prop 1 :|: Prop 3)]
    ["Distribution"]
    3

doubleNegation :: a === Not (Not a)
doubleNegation = IsoProof $ TypedProof
    [Prop 1, Not $ Not $ Prop 1]
    ["Double Negation"]
    1

transposition :: (a --> b) === (Not b --> Not a)
transposition = IsoProof $ TypedProof
    [Prop 1 :>: Prop 2, Not (Prop 2) :>: Not (Prop 1)]
    ["Transposition"]
    2

defImplication :: (a --> b) === (Not a \/ b)
defImplication = IsoProof $ TypedProof
    [Prop 1 :>: Prop 2, Not (Prop 1) :|: Prop 2]
    ["Definition of Implication"]
    2

matEquivalence :: (a <-> b) === ((a --> b) /\ (b --> a))
matEquivalence = IsoProof $ TypedProof
    [Prop 1 :=: Prop 2, (Prop 1 :>: Prop 2) :&: (Prop 2 :>: Prop 1)]
    ["Material Equivalence"]
    2

defEquivalence :: (a <-> b) === ((a /\ b) \/ (Not a /\ Not b))
defEquivalence = IsoProof $ TypedProof
    [Prop 1 :=: Prop 2, (Prop 1 :&: Prop 2) :|: (Not (Prop 1) :&: Not (Prop 2))]
    ["Definition of Equivalence"]
    2

exportation :: ((a /\ b) --> c) === (a --> (b --> c))
exportation = IsoProof $ TypedProof
    [(Prop 1 :&: Prop 2) :>: Prop 3, Prop 1 :>: (Prop 2 :>: Prop 3)]
    ["Exportation"]
    3

idempotenceOr :: a === (a \/ a)
idempotenceOr = IsoProof $ TypedProof
    [Prop 1, Prop 1 :|: Prop 1]
    ["Idempotence"]
    1

idempotenceAnd :: a === (a /\ a)
idempotenceAnd = IsoProof $ TypedProof
    [Prop 1, Prop 1 :&: Prop 1]
    ["Idempotence"]
    1

simplification :: (a /\ b) |- a
simplification = TypedProof
    [Prop 1 :&: Prop 2, Prop 1]
    ["Simplification"]
    2

addition :: a |- (a \/ b)
addition = TypedProof
    [Prop 1, Prop 1 :|: Prop 2]
    ["Addition"]
    2
