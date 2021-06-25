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
	singletonClause,
	insertClause,
	addClause,
	addAll,
	toDNF
) where

import Control.Monad (foldM)
import Control.Monad.Writer (Writer)
import qualified Control.Monad.Writer as W
import Control.Category ((>>>))
import Data.List (isSubsequenceOf, partition)

import WFF (WFF(..))
import WFFType
import DirectedProof (DirectedProof, EquivProof)
import qualified DirectedProof as D
import TypedProof (type (-||-)(), type (|-)())
import qualified TypedProof as T
import ReLabel (SmartIndex(..))

type EW x = Writer (EquivProof (SmartIndex x))
type DW x = Writer (DirectedProof (SmartIndex x))

toDW :: EW x v -> DW x v
toDW = W.mapWriter $ fmap D.toDirected

{-
	A disjunction of conjunctions of atoms of the form A or Not A.
	All lists should be sorted and represent right associative formulae.
	e.g. A /\ (B /\ ~A) is [(A,True),(B,True),(A,False)]
-}
newtype Clause x = Clause { atoms :: [(x,Bool)] } deriving (Show, Eq, Ord)
newtype DNF x = DNF { clauses :: [Clause x] } deriving Show

-- Removes the first clause from a DNF
pop :: DNF x -> Maybe (DNF x)
pop (DNF []) = error "Invalid DNF"
pop (DNF [_]) = Nothing
pop (DNF (_:cs)) = Just $ DNF cs

{-
	Bring atoms in the sorted list to the front of the clause,
	returning the clause without those atoms.
	Result is of the form Removed /\ Kept.
-}
bringForward :: Ord x => [(SmartIndex x,Bool)] -> Clause (SmartIndex x) ->
	EW x (Clause (SmartIndex x))
bringForward _ (Clause []) = error "Invalid clause"
bringForward [] clause = return clause
bringForward _ clause@(Clause [_]) = return clause -- Cannot remove all elements
bringForward leftss@(left:lefts) clause@(Clause (right:rights))
	| left < right = bringForward lefts clause
	| left == right = do
		nrights <- W.censor D.liftAndRight $ bringForward lefts $ Clause rights
		W.tell $ Index <$> D.fromIso
			(T.association :: a /\ (b /\ c) -||- (a /\ b) /\ c)
		return nrights
	| rights `isSubsequenceOf` leftss = do
		W.tell $ Index <$> D.fromIso (T.commutation :: a /\ b -||- b /\ a)
		return $ Clause [right]
	| otherwise = do
		Clause nrights <- W.censor D.liftAndRight $ bringForward leftss $
			Clause rights
		W.tell $ Index <$> D.fromIso (
			T.association >>>
			T.liftLeft T.commutation >>>
			T.invert T.association
			:: a /\ (b /\ c) -||- b /\ (a /\ c)
			)
		return $ Clause $ right:nrights

{-
	Removes atoms in the sorted list from a clause, assuming there is only one
	clause in the formula.
-}
removeAtomsAlone :: Ord x => [(SmartIndex x,Bool)] -> Clause (SmartIndex x) ->
	DW x (Clause (SmartIndex x))
removeAtomsAlone _ (Clause []) = error "Invalid clause"
removeAtomsAlone [] clause = return clause
removeAtomsAlone _ clause@(Clause [_]) =
	return clause -- Cannot remove all elements
removeAtomsAlone removess@(remove:removes) clause@(Clause (atom:atos))
	| remove < atom = removeAtomsAlone removes clause
	| remove == atom = do
		W.tell $ Index <$> D.fromTyped (
			T.toTyped T.commutation >>>
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
			T.toTyped T.commutation >>>
			T.simplification
			:: a /\ b |- b
			)
		return nclause

{-
	Removes atoms in the sorted list from a clause, assuming the formula is of
	the form clause \/ other
-}
removeAtoms :: Ord x => [(SmartIndex x,Bool)] -> Clause (SmartIndex x) ->
	DW x (Clause (SmartIndex x))
removeAtoms _ (Clause []) = error "Invalid clause"
removeAtoms [] clause = return clause
removeAtoms _ clause@(Clause [_]) = return clause -- Cannot remove all elements
removeAtoms removess@(remove:removes) clause@(Clause (atom:atos))
	| remove < atom = removeAtoms removes clause
	| remove == atom = do
		W.tell $ Index <$> D.fromTyped (
			T.toTyped
				(T.commutation >>> T.distribution >>> T.commutation) >>>
			T.simplification >>>
			T.toTyped T.commutation
			:: (a /\ b) \/ c |- b \/ c
			)
		removeAtoms removes $ Clause atos
	| atos `isSubsequenceOf` removess = do
		W.tell $ Index <$> D.fromTyped (
			T.toTyped (T.commutation >>> T.distribution) >>>
			T.simplification >>>
			T.toTyped T.commutation
			:: (a /\ b) \/ c |- a \/ c
			)
		return $ Clause [atom]
	| otherwise = do
		nclause <- toDW $ bringForward removess $ Clause atos
		W.tell $ Index <$> D.fromTyped (
			T.toTyped
				(T.commutation >>> T.distribution >>> T.commutation) >>>
			T.simplification >>>
			T.toTyped T.commutation
			:: (a /\ b) \/ c |- b \/ c
			)
		return nclause

-- A DNF with one Clause
singleton :: Clause x -> DNF x
singleton = DNF . pure

-- A Clause with one Atom
singletonClause :: (x, Bool) -> Clause x
singletonClause = Clause . pure

-- Adds a clause to a DNF, with the proof starting from (clause \/ dnf)
insertClause :: Ord x => Clause (SmartIndex x) -> DNF (SmartIndex x) ->
	EW x (DNF (SmartIndex x))
insertClause _ (DNF []) = error "Invalid DNF"
insertClause clause dnf@(DNF [right])
	| clause < right = return $ DNF [clause,right]
	| clause == right = do
		W.tell $ Index <$> D.fromIso (T.invert T.idempotence :: a \/ a -||- a)
		return dnf
	| otherwise = do
		W.tell $ Index <$> D.fromIso (T.commutation :: a \/ b -||- b \/ a)
		return $ DNF [right, clause]
insertClause clause dnf@(DNF rightss@(right:rights))
	| clause < right = return $ DNF $ clause:rightss
	| clause == right = do
		W.tell $ Index <$> D.fromIso (
			T.association >>> T.liftLeft (T.invert T.idempotence)
			:: a \/ (a \/ b) -||- a \/ b
			)
		return dnf
	| otherwise = do
		W.tell $ Index <$> D.fromIso (
			T.association >>>
			T.liftLeft T.commutation >>>
			T.invert T.association
			:: a \/ (b \/ c) -||- b \/ (a \/ c)
			)
		DNF . (right:) . clauses <$>
			W.censor D.liftOrRight (insertClause clause $ DNF rights)

{-
	Adds a clause to the end of a DNF, with the proof starting from
	DNF \/ newClause
-}
addEnd :: Ord x => DNF (SmartIndex x) -> EquivProof (SmartIndex x)
addEnd (DNF []) = error "Invalid DNF"
addEnd (DNF [_]) = mempty
addEnd (DNF (_:cs)) = mconcat
	[ Index <$> D.fromIso
		(T.invert T.association :: (a \/ b) \/ c -||- a \/ (b \/ c))
	, D.liftOrRight (addEnd $ DNF cs)
	]

-- Adds a clause to a DNF, with the proof starting from the DNF alone
addClause :: Ord x => Clause (SmartIndex x) -> DNF (SmartIndex x) ->
	DW x (DNF (SmartIndex x))
addClause clause dnf = do
	W.tell $ Index <$> D.fromTyped (
		T.addition >>>
		T.toTyped T.commutation
		:: a |- b \/ a
		)
	toDW $ insertClause clause dnf

{-
	Adds a sorted list of clauses to a DNF, with the proof starting from the
	DNF alone
-}
addAll :: Ord x => [Clause (SmartIndex x)] -> DNF (SmartIndex x) ->
	DW x (DNF (SmartIndex x))
addAll cs dnf = case partition (<= largest) cs of
	([], []) -> return dnf
	([], _) -> do
		W.tell $ Index <$> D.fromTyped (T.addition :: a |- a \/ b)
		W.tell $ D.toDirected $ addEnd dnf
		return $ DNF $ clauses dnf ++ cs
	(_, []) -> do
		foldM (flip addClause) dnf cs
	(smalls, larges) -> do
		W.tell $ Index <$> D.fromTyped (T.addition :: a |- a \/ b)
		W.tell $ D.toDirected $ addEnd dnf
		foldM (flip addClause) (DNF $ clauses dnf ++ larges) smalls
	where
		largest = last $ clauses dnf

-- Remove all implications and equivalences from a formula
removeImpEq :: Ord x => WFF (SmartIndex x) -> EW x (WFF (SmartIndex x))
removeImpEq (left :>: right) = do
	nleft <- W.censor D.liftImpliesLeft $ removeImpEq left
	nright <- W.censor D.liftImpliesRight $ removeImpEq right
	W.tell $ Index <$> D.fromIso (T.defImplication :: a --> b -||- Not a \/ b)
	return $ Not nleft :|: nright
removeImpEq (left :=: right) = do
	nleft <- W.censor D.liftEquivLeft $ removeImpEq left
	nright <- W.censor D.liftEquivRight $ removeImpEq right
	W.tell $ Index <$> D.fromIso
		(T.defEquivalence :: a <-> b -||- (a /\ b) \/ (Not a /\ Not b))
	return $ (nleft :&: nright) :|: (Not nleft :&: Not nright)
removeImpEq (left :|: right) = do
	nleft <- W.censor D.liftOrLeft $ removeImpEq left
	nright <- W.censor D.liftOrRight $ removeImpEq right
	return $ nleft :|: nright
removeImpEq (left :&: right) = do
	nleft <- W.censor D.liftAndLeft $ removeImpEq left
	nright <- W.censor D.liftAndRight $ removeImpEq right
	return $ nleft :&: nright
removeImpEq (Not w) = Not <$> W.censor D.liftNot (removeImpEq w)
removeImpEq w@(Prop _) = return w

-- Move all negations next to atoms in a formula
moveNotIn :: Ord x => WFF (SmartIndex x) -> EW x (WFF (SmartIndex x))
moveNotIn (Not (Not w)) = do
	W.tell $ Index <$> D.fromIso (T.invert T.doubleNegation :: Not (Not a) -||- a)
	moveNotIn w
moveNotIn (Not (left :|: right)) = do
	W.tell $ Index <$> D.fromIso (T.deMorgans :: Not (a \/ b) -||- Not a /\ Not b)
	moveNotIn $ Not left :&: Not right
moveNotIn (Not (left :&: right)) = do
	W.tell $ Index <$> D.fromIso (T.deMorgans :: Not (a /\ b) -||- Not a \/ Not b)
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
		(T.distribution :: a /\ (b \/ c) -||- (a /\ b) \/ (a /\ c))
	moveAndIn $ (na :&: nb) :|: (na :&: nc)
moveAndIn (left@(_ :|: _) :&: right) = do
	W.tell $ Index <$> D.fromIso (T.commutation :: a /\ b -||- b /\ a)
	moveAndIn $ right :&: left
moveAndIn (left :&: right) = do
	nleft <- W.censor D.liftAndLeft $ moveAndIn left
	nright <- W.censor D.liftAndRight $ moveAndIn right
	if nleft == left && nright == right then
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

-- Turns each clause into a right associative sorted clause
sortEachClause :: Ord x => WFF (SmartIndex x) ->
	EW x (WFF (Clause (SmartIndex x)))
sortEachClause (left :|: right) = do
	nleft <- W.censor D.liftOrLeft $ sortEachClause left
	nright <- W.censor D.liftOrRight $ sortEachClause right
	return $ nleft :|: nright
sortEachClause w = Prop . Clause <$> sortClause w

-- Turns one clause into a right associative sorted clause
sortClause :: Ord x => WFF (SmartIndex x) -> EW x [(SmartIndex x, Bool)]
sortClause (left :&: right) = do
	nleft <- W.censor D.liftAndLeft $ sortClause left
	nright <- W.censor D.liftAndRight $ sortClause right
	mergeClauses nleft nright
sortClause (Not (Prop p)) = return [(p, False)]
sortClause (Prop p) = return [(p, True)]
sortClause _ = error "Formula is not in DNF after conversion"

-- Merge two right associative clauses into one
mergeClauses :: Ord x => [(SmartIndex x, Bool)] -> [(SmartIndex x, Bool)] ->
	EW x [(SmartIndex x, Bool)]
mergeClauses [] _ = error "Invalid clause"
mergeClauses _ [] = error "Invalid clause"
mergeClauses [left] [right]
	| left < right = return [left,right]
	| left == right = do
		W.tell $ Index <$> D.fromIso (T.invert T.idempotence :: a /\ a -||- a)
		return [left]
	| otherwise = do
		W.tell $ Index <$> D.fromIso (T.commutation :: a /\ b -||- b /\ a)
		return [right, left]
mergeClauses [left] rightss@(right:rights)
	| left < right = return $ left:rightss
	| left == right = do
		W.tell $ Index <$> D.fromIso (
			T.association >>> T.liftLeft (T.invert T.idempotence)
			:: a /\ (a /\ b) -||- a /\ b
			)
		return rightss
	| otherwise = do
		W.tell $ Index <$> D.fromIso (
			T.association >>>
			T.liftLeft T.commutation >>>
			T.invert T.association
			:: a /\ (b /\ c) -||- b /\ (a /\ c)
			)
		(right:) <$> W.censor D.liftAndRight (mergeClauses [left] rights)
mergeClauses leftss@(left:lefts) [right]
	| left < right = do
		W.tell $ Index <$> D.fromIso
			(T.invert T.association :: (a /\ b) /\ c -||- a /\ (b /\ c))
		(left:) <$> W.censor D.liftAndRight (mergeClauses lefts [right])
	| left == right = do
		W.tell $ Index <$> D.fromIso (
			T.commutation >>>
			T.association >>>
			T.liftLeft (T.invert T.idempotence)
			:: (a /\ b) /\ a -||- a /\ b
			)
		return leftss
	| otherwise = do
		W.tell $ Index <$> D.fromIso (T.commutation :: a /\ b -||- b /\ a)
		return $ right:leftss
mergeClauses leftss@(left:lefts) rightss@(right:rights)
	| left < right = do
		W.tell $ Index <$> D.fromIso
			(T.invert T.association :: (a /\ b) /\ c -||- a /\ (b /\ c))
		(left:) <$> W.censor D.liftAndRight (mergeClauses lefts rightss)
	| left == right = do
		W.tell $ Index <$> D.fromIso (
			T.invert T.association >>>
			T.liftRight T.commutation >>>
			T.liftRight (T.invert T.association) >>>
			T.association >>>
			T.liftLeft (T.invert T.idempotence)
			:: (a /\ b) /\ (a /\ c) -||- a /\ (c /\ b)
			)
		(left:) <$> W.censor D.liftAndRight (mergeClauses rights lefts)
	| otherwise = do
		W.tell $ Index <$> D.fromIso (T.commutation :: a /\ b -||- b /\ a)
		mergeClauses rightss leftss

-- Turns a disjunction into a right associative sorted disjunction
sortClauses :: Ord x => WFF (Clause (SmartIndex x)) ->
	EW x [Clause (SmartIndex x)]
sortClauses (left :|: right) = do
	nleft <- W.censor D.liftOrLeft $ sortClauses left
	nright <- W.censor D.liftOrRight $ sortClauses right
	mergeDNF nleft nright
sortClauses (Prop w) = return [w]
sortClauses _ = error "Unsorted clause after sorting"

-- Merges two right associative disjuctions into one
mergeDNF :: Ord x => [Clause (SmartIndex x)] -> [Clause (SmartIndex x)] ->
	EW x [Clause (SmartIndex x)]
mergeDNF [] _ = error "Invalid DNF"
mergeDNF _ [] = error "Invalid DNF"
mergeDNF [left] [right]
	| left < right = return [left,right]
	| left == right = do
		W.tell $ Index <$> D.fromIso (T.invert T.idempotence :: a \/ a -||- a)
		return [left]
	| otherwise = do
		W.tell $ Index <$> D.fromIso (T.commutation :: a \/ b -||- b \/ a)
		return [right, left]
mergeDNF [left] rightss@(right:rights)
	| left < right = return $ left:rightss
	| left == right = do
		W.tell $ Index <$> D.fromIso (
			T.association >>> T.liftLeft (T.invert T.idempotence)
			:: a \/ (a \/ b) -||- a \/ b
			)
		return rightss
	| otherwise = do
		W.tell $ Index <$> D.fromIso (
			T.association >>>
			T.liftLeft T.commutation >>>
			T.invert T.association
			:: a \/ (b \/ c) -||- b \/ (a \/ c)
			)
		(right:) <$> W.censor D.liftOrRight (mergeDNF [left] rights)
mergeDNF leftss@(left:lefts) [right]
	| left < right = do
		W.tell $ Index <$> D.fromIso
			(T.invert T.association :: (a \/ b) \/ c -||- a \/ (b \/ c))
		(left:) <$> W.censor D.liftOrRight (mergeDNF lefts [right])
	| left == right = do
		W.tell $ Index <$> D.fromIso (
			T.commutation >>>
			T.association >>>
			T.liftLeft (T.invert T.idempotence)
			:: (a \/ b) \/ a -||- a \/ b
			)
		return leftss
	| otherwise = do
		W.tell $ Index <$> D.fromIso (T.commutation :: a \/ b -||- b \/ a)
		return $ right:leftss
mergeDNF leftss@(left:lefts) rightss@(right:rights)
	| left < right = do
		W.tell $ Index <$> D.fromIso
			(T.invert T.association :: (a \/ b) \/ c -||- a \/ (b \/ c))
		(left:) <$> W.censor D.liftOrRight (mergeDNF lefts rightss)
	| left == right = do
		W.tell $ Index <$> D.fromIso (
			T.invert T.association >>>
			T.liftRight T.commutation >>>
			T.liftRight (T.invert T.association) >>>
			T.association >>>
			T.liftLeft (T.invert T.idempotence)
			:: (a \/ b) \/ (a \/ c) -||- a \/ (c \/ b)
			)
		(left:) <$> W.censor D.liftOrRight (mergeDNF rights lefts)
	| otherwise = do
		W.tell $ Index <$> D.fromIso (T.commutation :: a \/ b -||- b \/ a)
		mergeDNF rightss leftss

-- Converts a formula to DNF, and returns a proof WFF -||- DNF
toDNF :: Ord x => WFF (SmartIndex x) -> EW x (DNF (SmartIndex x))
toDNF wff = W.censor (D.identity wff <>) $
	removeImpEq wff >>=
	moveNotIn >>=
	moveAndIn >>=
	sortEachClause >>=
	(sortClauses >>>
	fmap DNF)
