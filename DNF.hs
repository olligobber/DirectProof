{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

module DNF (
    EW,
    DW,
    toDW,
    Clause(atoms),
    DNF(clauses),
    pop,
    removeAtomsAlone,
    removeAtoms,
    singleton,
    insertClause,
    toDNF
) where

import Control.Monad.Writer (Writer)
import qualified Control.Monad.Writer as W
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import Control.Category ((>>>))
import Data.List (isSubsequenceOf)

import WFF (WFF(..))
import WFFType
import DirectedProof (DirectedProof, EquivProof)
import qualified DirectedProof as D
import TypedProof (type (|~)(), type (|-)())
import qualified TypedProof as T
import ReLabel (SmartIndex(..))

type EW x = Writer (EquivProof (SmartIndex x))
type DW x = Writer (DirectedProof (SmartIndex x))

toDW :: EW x v -> DW x v
toDW = W.mapWriter (\(r, p) -> (r, D.toDirected p))

-- A disjunction of conjunctions of atoms of the form A or Not A
-- All lists should be sorted and represent left associative formulae
newtype Clause x = Clause { atoms :: [(x,Bool)] } deriving (Show, Eq, Ord)
newtype DNF x = DNF { clauses :: [Clause x] } deriving Show

-- Removes the first clause from a DNF
pop :: DNF x -> Maybe (DNF x)
pop (DNF [_]) = Nothing
pop (DNF (_:clauses)) = Just $ DNF clauses

{-
    Bring atoms in the sorted list to the front of the clause,
    returning the clause without those atoms
-}
bringForward :: Ord x => [(SmartIndex x,Bool)] -> Clause (SmartIndex x) ->
    EW x (Clause (SmartIndex x))
bringForward [] clause = return clause
bringForward _ clause@(Clause [_]) = return clause -- Cannot remove all elements
bringForward leftss@(left:lefts) clause@(Clause (right:rights))
    | left < right = bringForward lefts clause
    | left == right = do
        nrights <- W.censor D.liftAndRight $ bringForward lefts $ Clause rights
        W.tell $ Index <$> D.fromIso
            (T.associationAnd :: a /\ (b /\ c) |~ (a /\ b) /\ c)
        return nrights
    | rights `isSubsequenceOf` leftss = do
        W.tell $ Index <$> D.fromIso (T.commutationAnd :: a /\ b |~ b /\ a)
        return $ Clause [right]
    | otherwise = do
        Clause nrights <- W.censor D.liftAndRight $ bringForward leftss $
            Clause rights
        W.tell $ Index <$> D.fromIso (
            T.associationAnd >>>
            T.liftAndLeft T.commutationAnd >>>
            T.invert T.associationAnd
            :: a /\ (b /\ c) |~ b /\ (a /\ c)
            )
        return $ Clause $ right:nrights

-- Removes atoms in the sorted list from a clause, assuming the formula is alone
removeAtomsAlone :: Ord x => [(SmartIndex x,Bool)] -> Clause (SmartIndex x) ->
    DW x (Clause (SmartIndex x))
removeAtomsAlone [] clause = return clause
removeAtomsAlone _ clause@(Clause [_]) =
    return clause -- Cannot remove all elements
removeAtomsAlone removess@(remove:removes) clause@(Clause (atom:atos))
    | remove < atom = removeAtomsAlone removes clause
    | remove == atom = do
        W.tell $ Index <$> D.fromTyped (
            T.toTyped T.commutationAnd >>>
            T.simplification
            :: a /\ b |- b
            )
        removeAtomsAlone removes $ Clause atos
    | atos `isSubsequenceOf` removess = do
        W.tell $ Index <$> D.fromTyped (T.simplification :: a /\ b |- a)
        return $ Clause [atom]
    | otherwise = do
        nclause <- toDW $ bringForward removess $ Clause atos
        W.tell $ Index <$> D.fromTyped (
            T.toTyped T.commutationAnd >>>
            T.simplification
            :: a /\ b |- b
            )
        return $ nclause

-- Removes atoms in the sorted list from a clause, assuming the formula is of
-- the form clause | other
removeAtoms :: Ord x => [(SmartIndex x,Bool)] -> Clause (SmartIndex x) ->
    DW x (Clause (SmartIndex x))
removeAtoms [] clause = return clause
removeAtoms _ clause@(Clause [_]) = return clause -- Cannot remove all elements
removeAtoms removess@(remove:removes) clause@(Clause (atom:atos))
    | remove < atom = removeAtoms removes clause
    | remove == atom = do
        W.tell $ Index <$> D.fromTyped (
            T.toTyped
                (T.commutationOr >>> T.distribution2 >>> T.commutationAnd) >>>
            T.simplification >>>
            T.toTyped T.commutationOr
            :: (a /\ b) \/ c |- b \/ c
            )
        removeAtoms removes $ Clause atos
    | atos `isSubsequenceOf` removess = do
        W.tell $ Index <$> D.fromTyped (
            T.toTyped (T.commutationOr >>> T.distribution2) >>>
            T.simplification >>>
            T.toTyped T.commutationOr
            :: (a /\ b) \/ c |- a \/ c
            )
        return $ Clause [atom]
    | otherwise = do
        nclause <- toDW $ bringForward removess $ Clause atos
        W.tell $ Index <$> D.fromTyped (
            T.toTyped
                (T.commutationOr >>> T.distribution2 >>> T.commutationAnd) >>>
            T.simplification >>>
            T.toTyped T.commutationOr
            :: (a /\ b) \/ c |- b \/ c
            )
        return $ nclause

singleton :: Clause x -> DNF x
singleton = DNF . pure

-- Adds a clause to a DNF, with the proof starting from (clause | dnf)
insertClause :: Ord x => Clause (SmartIndex x) -> DNF (SmartIndex x) ->
    EW x (DNF (SmartIndex x))
insertClause clause dnf@(DNF [right])
    | clause < right = return $ DNF [clause,right]
    | clause == right = do
        W.tell $ Index <$> D.fromIso (T.invert T.idempotenceOr :: a \/ a |~ a)
        return dnf
    | clause > right = do
        W.tell $ Index <$> D.fromIso (T.commutationOr :: a \/ b |~ b \/ a)
        return $ DNF [right, clause]
insertClause clause dnf@(DNF rightss@(right:rights))
    | clause < right = return $ DNF $ clause:rightss
    | clause == right = do
        W.tell $ Index <$> D.fromIso (
            T.associationOr >>> T.liftOrLeft (T.invert T.idempotenceOr)
            :: a \/ (a \/ b) |~ a \/ b
            )
        return dnf
    | clause > right = do
        W.tell $ Index <$> D.fromIso (
            T.associationOr >>>
            T.liftOrLeft T.commutationOr >>>
            T.invert T.associationOr
            :: a \/ (b \/ c) |~ b \/ (a \/ c)
            )
        DNF . (right:) . clauses <$>
            W.censor D.liftOrRight (insertClause clause $ DNF rights)

-- Remove all implications and equivalences
removeImpEq :: Ord x => WFF (SmartIndex x) -> EW x (WFF (SmartIndex x))
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
moveNotIn :: Ord x => WFF (SmartIndex x) -> EW x (WFF (SmartIndex x))
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
moveAndIn :: Ord x => WFF (SmartIndex x) -> EW x (WFF (SmartIndex x))
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
    EW x (WFF (Clause (SmartIndex x)))
sortEachClause (left :|: right) = do
    nleft <- W.censor D.liftOrLeft $ sortEachClause left
    nright <- W.censor D.liftOrRight $ sortEachClause right
    return $ nleft :|: nright
sortEachClause w = Prop . Clause <$> sortClause w

-- Turns one clause into a left associative sorted clause
sortClause :: Ord x => WFF (SmartIndex x) -> EW x [(SmartIndex x, Bool)]
sortClause (left :&: right) = do
    nleft <- W.censor D.liftAndLeft $ sortClause left
    nright <- W.censor D.liftAndRight $ sortClause right
    mergeClauses nleft nright
sortClause (Not (Prop p)) = return [(p, False)]
sortClause (Prop p) = return [(p, True)]
sortClause _ = error "Formula is not in DNF after conversion"

-- Merge two LASC into one LASC
mergeClauses :: Ord x => [(SmartIndex x, Bool)] -> [(SmartIndex x, Bool)] ->
    EW x [(SmartIndex x, Bool)]
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
sortClauses :: Ord x => WFF (Clause (SmartIndex x)) ->
    EW x [Clause (SmartIndex x)]
sortClauses (left :|: right) = do
    nleft <- W.censor D.liftOrLeft $ sortClauses left
    nright <- W.censor D.liftOrRight $ sortClauses right
    mergeDNF nleft nright
sortClauses (Prop w) = return [w]
sortClauses _ = error "Unsorted clause after sorting"

-- Merges two LASD into one LASD
mergeDNF :: Ord x => [Clause (SmartIndex x)] -> [Clause (SmartIndex x)] ->
    EW x [Clause (SmartIndex x)]
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
toDNF :: Ord x => WFF (SmartIndex x) -> EW x (DNF (SmartIndex x))
toDNF wff = W.censor (D.identity wff <>) $
    removeImpEq wff >>=
    moveNotIn >>=
    moveAndIn >>=
    sortEachClause >>=
    (sortClauses >>>
    fmap DNF)
