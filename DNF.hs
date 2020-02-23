{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

module DNF where

import Control.Monad.Writer (Writer)
import qualified Control.Monad.Writer as W
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import Control.Category ((>>>))

import WFF (WFF(..))
import WFFType
import DirectedProof (EquivProof)
import qualified DirectedProof as D
import TypedProof (type (|~)())
import qualified TypedProof as T
import ReLabel (SmartIndex(..))

-- A disjunction of conjunctions of atoms of the form A or Not A
-- All lists should be sorted and represent left associative formulae
newtype DNF x = DNF { clauses :: [[(x,Bool)]] } deriving Show

-- Remove all implications and equivalences
removeImpEq :: Ord x => WFF (SmartIndex x) ->
    Writer (EquivProof (SmartIndex x)) (WFF (SmartIndex x))
removeImpEq (left :>: right) = do
    nleft <- W.censor D.liftImpliesLeft $ removeImpEq left
    nright <- W.censor D.liftImpliesRight $ removeImpEq right
    W.tell $ Index <$> D.fromIso (T.defImplication :: a --> b |~ Not a \/ b)
    return $ Not nleft :|: nright
removeImpEq (left :=: right) = do
    nleft <- W.censor D.liftEquivLeft $ removeImpEq left
    nright <- W.censor D.liftEquivRight $ removeImpEq right
    W.tell $ Index <$> D.fromIso
        (T.defEquivalence :: a <-> b |~ (a /\ b) \/ (Not a /\ Not b))
    return $ (nleft :&: nright) :|: (Not nleft :&: Not nright)
removeImpEq (left :|: right) = do
    nleft <- W.censor D.liftOrLeft $ removeImpEq left
    nright <- W.censor D.liftOrRight $ removeImpEq right
    return $ nleft :|: nright
removeImpEq (left :&: right) = do
    nleft <- W.censor D.liftAndLeft $ removeImpEq left
    nright <- W.censor D.liftAndRight $ removeImpEq right
    return $ nleft :&: nright
removeImpEq (Not w) = Not <$> (W.censor D.liftNot $ removeImpEq w)
removeImpEq w@(Prop _) = return w

-- Move all negations next to atoms
moveNotIn :: Ord x => WFF (SmartIndex x) ->
    Writer (EquivProof (SmartIndex x)) (WFF (SmartIndex x))
moveNotIn (Not (Not w)) = do
    W.tell $ Index <$> D.fromIso (T.invert T.doubleNegation :: Not (Not a) |~ a)
    moveNotIn w
moveNotIn (Not (left :|: right)) = do
    W.tell $ Index <$> D.fromIso (T.deMorgans2 :: Not (a \/ b) |~ Not a /\ Not b)
    moveNotIn $ Not left :&: Not right
moveNotIn (Not (left :&: right)) = do
    W.tell $ Index <$> D.fromIso (T.deMorgans1 :: Not (a /\ b) |~ Not a \/ Not b)
    moveNotIn $ Not left :|: Not right
moveNotIn w@(Not (Prop _)) = return w
moveNotIn (left :|: right) = do
    nleft <- W.censor D.liftOrLeft $ moveNotIn left
    nright <- W.censor D.liftOrRight $ moveNotIn right
    return $ nleft :|: nright
moveNotIn (left :&: right) = do
    nleft <- W.censor D.liftAndLeft $ moveNotIn left
    nright <- W.censor D.liftAndRight $ moveNotIn right
    return $ nleft :&: nright
moveNotIn w@(Prop _) = return w
moveNotIn _ = error "Equivalence or implication found after all were removed"

-- Move ands in and ors out
moveAndIn :: Ord x => WFF (SmartIndex x) ->
    Writer (EquivProof (SmartIndex x)) (WFF (SmartIndex x))
moveAndIn (a :&: (b :|: c)) = do
    na <- W.censor D.liftAndLeft $ moveAndIn a
    nb <- W.censor (D.liftAndRight . D.liftOrLeft) $ moveAndIn b
    nc <- W.censor (D.liftAndRight . D.liftOrRight) $ moveAndIn c
    W.tell $ Index <$> D.fromIso
        (T.distribution1 :: a /\ (b \/ c) |~ (a /\ b) \/ (a /\ c))
    moveAndIn $ (na :&: nb) :|: (na :&: nc)
moveAndIn (left@(_ :|: _) :&: right) = do
    W.tell $ Index <$> D.fromIso (T.commutationAnd :: a /\ b |~ b /\ a)
    moveAndIn $ right :&: left
moveAndIn (left :&: right) = do
    nleft <- W.censor D.liftAndLeft $ moveAndIn left
    nright <- W.censor D.liftAndRight $ moveAndIn right
    if (nleft == left && nright == right) then
        return $ left :&: right
    else
        moveAndIn $ nleft :&: nright
moveAndIn (left :|: right) = do
    nleft <- W.censor D.liftOrLeft $ moveAndIn left
    nright <- W.censor D.liftOrRight $ moveAndIn right
    return $ nleft :|: nright
moveAndIn w@(Not (Prop _)) = return w
moveAndIn w@(Prop _) = return w
moveAndIn _ = error
    "Equivalence, implication, or negation found after all were removed"

-- Turns each clause into a left associative sorted clause
sortEachClause :: Ord x => WFF (SmartIndex x) ->
    Writer (EquivProof (SmartIndex x)) (WFF [(SmartIndex x, Bool)])
sortEachClause (left :|: right) = do
    nleft <- W.censor D.liftOrLeft $ sortEachClause left
    nright <- W.censor D.liftOrRight $ sortEachClause right
    return $ nleft :|: nright
sortEachClause w = Prop <$> sortClause w

-- Turns one clause into a left associative sorted clause
sortClause :: Ord x => WFF (SmartIndex x) ->
    Writer (EquivProof (SmartIndex x)) [(SmartIndex x, Bool)]
sortClause (left :&: right) = do
    nleft <- W.censor D.liftAndLeft $ sortClause left
    nright <- W.censor D.liftAndRight $ sortClause right
    mergeClauses nleft nright
sortClause (Not (Prop p)) = return [(p, False)]
sortClause (Prop p) = return [(p, True)]
sortClause _ = error "Formula is not in DNF after conversion"

-- Merge two LASC into one LASC
mergeClauses :: Ord x => [(SmartIndex x, Bool)] -> [(SmartIndex x, Bool)] ->
    Writer (EquivProof (SmartIndex x)) [(SmartIndex x, Bool)]
mergeClauses [left] [right]
    | left < right = return [left,right]
    | left == right = do
        W.tell $ Index <$> D.fromIso (T.invert T.idempotenceAnd :: a /\ a |~ a)
        return [left]
    | left > right = do
        W.tell $ Index <$> D.fromIso (T.commutationAnd :: a /\ b |~ b /\ a)
        return [right, left]
mergeClauses [left] rightss@(right:rights)
    | left < right = return $ left:rightss
    | left == right = do
        W.tell $ Index <$> D.fromIso (
            T.associationAnd >>> T.liftAndLeft (T.invert T.idempotenceAnd)
            :: a /\ (a /\ b) |~ a /\ b
            )
        return rightss
    | left > right = do
        W.tell $ Index <$> D.fromIso (
            T.associationAnd >>>
            T.liftAndLeft T.commutationAnd >>>
            T.invert T.associationAnd
            :: a /\ (b /\ c) |~ b /\ (a /\ c)
            )
        (right:) <$> (W.censor D.liftAndRight $ mergeClauses [left] rights)
mergeClauses leftss@(left:lefts) [right]
    | left < right = do
        W.tell $ Index <$> D.fromIso
            (T.invert T.associationAnd :: (a /\ b) /\ c |~ a /\ (b /\ c))
        (left:) <$> (W.censor D.liftAndRight $ mergeClauses lefts [right])
    | left == right = do
        W.tell $ Index <$> D.fromIso (
            T.commutationAnd >>>
            T.associationAnd >>>
            T.liftAndLeft (T.invert T.idempotenceAnd)
            :: (a /\ b) /\ a |~ a /\ b
            )
        return leftss
    | left > right = do
        W.tell $ Index <$> D.fromIso (T.commutationAnd :: a /\ b |~ b /\ a)
        return $ right:leftss
mergeClauses leftss@(left:lefts) rightss@(right:rights)
    | left < right = do
        W.tell $ Index <$> D.fromIso
            (T.invert T.associationAnd :: (a /\ b) /\ c |~ a /\ (b /\ c))
        (left:) <$> (W.censor D.liftAndRight $ mergeClauses lefts rightss)
    | left == right = do
        W.tell $ Index <$> D.fromIso (
            T.invert T.associationAnd >>>
            T.liftAndRight T.commutationAnd >>>
            T.liftAndRight (T.invert T.associationAnd) >>>
            T.associationAnd >>>
            T.liftAndLeft (T.invert T.idempotenceAnd)
            :: (a /\ b) /\ (a /\ c) |~ a /\ (c /\ b)
            )
        (left:) <$> (W.censor D.liftAndRight $ mergeClauses rights lefts)
    | left > right = do
        W.tell $ Index <$> D.fromIso (T.commutationAnd :: a /\ b |~ b /\ a)
        mergeClauses rightss leftss

-- Turns a disjunction into a left associative sorted disjunction
sortClauses :: Ord x => WFF [(SmartIndex x, Bool)] ->
    Writer (EquivProof (SmartIndex x)) [[(SmartIndex x, Bool)]]
sortClauses (left :|: right) = do
    nleft <- W.censor D.liftOrLeft $ sortClauses left
    nright <- W.censor D.liftOrRight $ sortClauses right
    mergeDNF nleft nright
sortClauses (Prop w) = return [w]
sortClauses _ = error "Unsorted clause after sorting"

-- Merges two LASD into one LASD
mergeDNF :: Ord x => [[(SmartIndex x, Bool)]] -> [[(SmartIndex x, Bool)]] ->
    Writer (EquivProof (SmartIndex x)) [[(SmartIndex x, Bool)]]
mergeDNF [left] [right]
    | left < right = return [left,right]
    | left == right = do
        W.tell $ Index <$> D.fromIso (T.invert T.idempotenceOr :: a \/ a |~ a)
        return [left]
    | left > right = do
        W.tell $ Index <$> D.fromIso (T.commutationOr :: a \/ b |~ b \/ a)
        return [right, left]
mergeDNF [left] rightss@(right:rights)
    | left < right = return $ left:rightss
    | left == right = do
        W.tell $ Index <$> D.fromIso (
            T.associationOr >>> T.liftOrLeft (T.invert T.idempotenceOr)
            :: a \/ (a \/ b) |~ a \/ b
            )
        return rightss
    | left > right = do
        W.tell $ Index <$> D.fromIso (
            T.associationOr >>>
            T.liftOrLeft T.commutationOr >>>
            T.invert T.associationOr
            :: a \/ (b \/ c) |~ b \/ (a \/ c)
            )
        (right:) <$> (W.censor D.liftOrRight $ mergeDNF [left] rights)
mergeDNF leftss@(left:lefts) [right]
    | left < right = do
        W.tell $ Index <$> D.fromIso
            (T.invert T.associationOr :: (a \/ b) \/ c |~ a \/ (b \/ c))
        (left:) <$> (W.censor D.liftOrRight $ mergeDNF lefts [right])
    | left == right = do
        W.tell $ Index <$> D.fromIso (
            T.commutationOr >>>
            T.associationOr >>>
            T.liftOrLeft (T.invert T.idempotenceOr)
            :: (a \/ b) \/ a |~ a \/ b
            )
        return leftss
    | left > right = do
        W.tell $ Index <$> D.fromIso (T.commutationOr :: a \/ b |~ b \/ a)
        return $ right:leftss
mergeDNF leftss@(left:lefts) rightss@(right:rights)
    | left < right = do
        W.tell $ Index <$> D.fromIso
            (T.invert T.associationOr :: (a \/ b) \/ c |~ a \/ (b \/ c))
        (left:) <$> (W.censor D.liftOrRight $ mergeDNF lefts rightss)
    | left == right = do
        W.tell $ Index <$> D.fromIso (
            T.invert T.associationOr >>>
            T.liftOrRight T.commutationOr >>>
            T.liftOrRight (T.invert T.associationOr) >>>
            T.associationOr >>>
            T.liftOrLeft (T.invert T.idempotenceOr)
            :: (a \/ b) \/ (a \/ c) |~ a \/ (c \/ b)
            )
        (left:) <$> (W.censor D.liftOrRight $ mergeDNF rights lefts)
    | left > right = do
        W.tell $ Index <$> D.fromIso (T.commutationOr :: a \/ b |~ b \/ a)
        mergeDNF rightss leftss

-- Converts a formula to DNF and returns a proof WFF |~ DNF
toDNF :: Ord x => WFF (SmartIndex x) ->
    (DNF (SmartIndex x), EquivProof (SmartIndex x))
toDNF wff = W.runWriter (
    removeImpEq wff >>=
    moveNotIn >>=
    moveAndIn >>=
    sortEachClause >>=
    (sortClauses >>>
    fmap DNF)
    )
