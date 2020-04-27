{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

module DNFConvert (
	DW,
	convertDNF
) where

import Data.List (groupBy, isSubsequenceOf, maximumBy, (\\))
import Data.Function (on)
import qualified Control.Monad.Writer as W
import Control.Category ((>>>))

import DNF
import WFFType
import qualified DirectedProof as D
import TypedProof (type (|~)(), type (|-)())
import qualified TypedProof as T
import ReLabel (SmartIndex(..))

{-
	Represents a partly done conversion, with the formula
		inP \/ (conv \/ unconv).
	If one is missing, form is a \/ b.
	If two are missing, form is a.
	Three should never be missing.
-}
data DNFConversion x = DNFConversion {
	-- Clause currently being converted
	inProgress :: Maybe (Clause (SmartIndex x)),
	-- Previously converted clauses
	converted :: Maybe (DNF (SmartIndex x)),
	-- Clauses yet to be converted
	unconverted :: Maybe (DNF (SmartIndex x))
} deriving Show

-- Start the conversion process of a DNF
startConversion :: DNF (SmartIndex x) -> DNFConversion x
startConversion dnf = DNFConversion
	(Just $ head $ clauses dnf)
	Nothing
	(pop dnf)

{-
	Move inProgress to converted and get something from unconverted to make
	progress on
-}
nextProgress :: Ord x => DNFConversion x ->
	EW x (Either (DNF (SmartIndex x)) (DNFConversion x))
nextProgress (DNFConversion Nothing Nothing Nothing) = error
	"Everything has been deleted, cannot progress"
nextProgress (DNFConversion Nothing Nothing (Just uncon)) =
	return $ Right $ DNFConversion
		(Just $ head $ clauses uncon)
		Nothing
		(pop uncon)
nextProgress (DNFConversion Nothing (Just conv) Nothing) =
	return $ Left conv
nextProgress (DNFConversion Nothing (Just conv) (Just uncon)) =
	case clauses uncon of
		[] -> error "Invalid DNF"
		[unc] -> do
			W.tell $ Index <$> D.fromIso (T.commutation :: a \/ b |~ b \/ a)
			return $ Right $ DNFConversion (Just unc) (Just conv) Nothing
		unc:_ -> do
			W.tell $ Index <$> D.fromIso (
				T.liftRight T.commutation >>>
				T.association >>>
				T.commutation
				:: a \/ (b \/ c) |~ b \/ (a \/ c)
				)
			return $ Right $ DNFConversion (Just unc) (Just conv) (pop uncon)
nextProgress (DNFConversion (Just c) Nothing Nothing) =
	return $ Left $ singleton c
nextProgress (DNFConversion (Just c) (Just conv) Nothing) =
	Left <$> insertClause c conv
nextProgress (DNFConversion (Just c) Nothing (Just uncon)) =
	case clauses uncon of
		[] -> error "Invalid DNF"
		[unc] -> do
			W.tell $ Index <$> D.fromIso (T.commutation :: a \/ b |~ b \/ a)
			return $ Right $ DNFConversion
				(Just unc)
				(Just $ singleton c)
				Nothing
		unc:_ -> do
			W.tell $ Index <$> D.fromIso (
				T.association >>>
				T.liftLeft T.commutation >>>
				T.invert T.association
				:: a \/ (b \/ c) |~ b \/ (a \/ c)
				)
			return $ Right $ DNFConversion
				(Just unc)
				(Just $ singleton c)
				(pop uncon)
nextProgress (DNFConversion (Just c) (Just conv) (Just uncon)) =
	case clauses uncon of
		[] -> error "Invalid DNF"
		[unc] -> do
			W.tell $ Index <$> D.fromIso (
				T.association >>>
				T.commutation
				:: a \/ (b \/ c) |~ c \/ (a \/ b)
				)
			nconv <- W.censor D.liftOrRight $ insertClause c conv
			return $ Right $ DNFConversion (Just unc) (Just nconv) Nothing
		unc:_ -> do
			W.tell $ Index <$> D.fromIso (
				T.liftRight
					(T.liftRight T.commutation >>> T.association) >>>
				T.association >>>
				T.commutation >>>
				T.liftRight T.association
				:: a \/ (b \/ (c \/ d)) |~ c \/ ((a \/ b) \/ d)
				)
			nconv <- W.censor (D.liftOrRight . D.liftOrLeft) $
				insertClause c conv
			return $ Right $ DNFConversion (Just unc) (Just nconv) (pop uncon)

{-
	Check if a clause contains two opposite atoms and return the proposition
	involved
-}
getContradiction :: Eq x => Clause x -> Maybe x
getContradiction clause = case
	filter ((==2) . length) $ groupBy ((==) `on` fst) $ atoms clause of
		[] -> Nothing
		[]:_ -> error "Empty contradiction"
		((p,_):_):_ -> Just p

-- Check if the second is a subclause of the first
isSubClause :: Eq x => Clause x -> Clause x -> Bool
isSubClause = flip (isSubsequenceOf `on` atoms)

-- Find the longest subclause of the given clause from a DNF
bestSubClause :: Eq x => Clause x -> DNF x -> Maybe (Clause x)
bestSubClause clause dnf = case filter (isSubClause clause) $ clauses dnf of
	[] -> Nothing
	cs -> Just $ maximumBy (compare `on` length . atoms) cs

-- Update inProgress, given the goal dnf
makeProgress :: Ord x => DNF (SmartIndex x) -> DNFConversion x ->
	DW x (DNFConversion x)
makeProgress _ dnfc@(DNFConversion Nothing _ _) = return dnfc
makeProgress goal (DNFConversion (Just inP) Nothing Nothing) =
	case (getContradiction inP, bestSubClause inP goal) of
		(Nothing, Nothing) -> error "Unable to convert DNF"
		(Just p, _) -> do
			ninP <- removeAtoms (takeWhile ((/= p) . fst) $ atoms inP) inP
			_ <- addClause (singletonClause (Index 1, True)) $ singleton ninP
			if length (atoms ninP) == 2 then
				W.tell $ Index <$> (D.toDirected . D.fromIso) (
					T.commutation >>>
					T.distribution
					:: (Not a /\ a) \/ b |~ (b \/ Not a) /\ (b \/ a)
					)
			else
				W.tell $ Index <$> D.fromTyped (
					T.toTyped (
						T.commutation >>>
						T.distribution >>>
						T.liftRight T.distribution >>>
						T.association
						) >>>
					T.simplification
					:: (Not a /\ (a /\ b)) \/ c |- (c \/ Not a) /\ (c \/ a)
					)
			W.tell $ Index <$> D.fromTyped (
				T.toTyped (
					T.liftLeft (
						T.liftLeft T.doubleNegation >>>
						T.invert T.defImplication
						) >>>
					T.liftRight (
						T.commutation >>>
						T.liftLeft T.doubleNegation >>>
						T.invert T.defImplication
						)
					) >>>
				T.hypotheticalS
					(T.simplification)
					(T.toTyped T.commutation >>> T.simplification)
				>>>
				T.toTyped (
					T.defImplication >>>
					T.liftLeft (T.invert T.doubleNegation) >>>
					T.invert T.idempotence
					)
				:: (b \/ Not a) /\ (b \/ a) |- b
				)
			return $ DNFConversion Nothing (Just goal) Nothing
		(_, Just c) -> do
			ninP <- removeAtomsAlone (atoms inP \\ atoms c) inP
			return $ DNFConversion (Just ninP) Nothing Nothing
makeProgress goal (DNFConversion (Just inP) conv unconv) =
	case (getContradiction inP, bestSubClause inP goal) of
		(Nothing, Nothing) -> error "Unable to convert DNF"
		(Just p, _) -> do
			ninP <- removeAtoms (takeWhile ((/= p) . fst) $ atoms inP) inP
			if length (atoms ninP) == 2 then
				W.tell $ Index <$> (D.toDirected . D.fromIso) (
					T.commutation >>>
					T.distribution
					:: (Not a /\ a) \/ b |~ (b \/ Not a) /\ (b \/ a)
					)
			else
				W.tell $ Index <$> D.fromTyped (
					T.toTyped (
						T.commutation >>>
						T.distribution >>>
						T.liftRight T.distribution >>>
						T.association
						) >>>
					T.simplification
					:: (Not a /\ (a /\ b)) \/ c |- (c \/ Not a) /\ (c \/ a)
					)
			W.tell $ Index <$> D.fromTyped (
				T.toTyped (
					T.liftLeft (
						T.liftLeft T.doubleNegation >>>
						T.invert T.defImplication
						) >>>
					T.liftRight (
						T.commutation >>>
						T.liftLeft T.doubleNegation >>>
						T.invert T.defImplication
						)
					) >>>
				T.hypotheticalS
					(T.simplification)
					(T.toTyped T.commutation >>> T.simplification)
				>>>
				T.toTyped (
					T.defImplication >>>
					T.liftLeft (T.invert T.doubleNegation) >>>
					T.invert T.idempotence
					)
				:: (b \/ Not a) /\ (b \/ a) |- b
				)
			return $ DNFConversion Nothing conv unconv
		(_, Just c) -> do
			ninP <- removeAtoms (atoms inP \\ atoms c) inP
			return $ DNFConversion (Just ninP) conv unconv

-- Complete conversion to goal dnf, but possibly missing some clauses
finishConversion :: Ord x => DNFConversion x -> DNF (SmartIndex x) ->
	DW x (DNF (SmartIndex x))
finishConversion dnfc goal = do
	next <- makeProgress goal dnfc >>= toDW . nextProgress
	case next of
		Left dnf -> return dnf
		Right nextdnfc -> finishConversion nextdnfc goal

-- Adds clauses to the first dnf until it matches the second
addUntil :: Ord x => DNF (SmartIndex x) -> DNF (SmartIndex x) ->
	DW x (DNF (SmartIndex x))
addUntil start goal = addAll (clauses goal \\ clauses start) start

-- Completely convert one DNF to another
convertDNF :: Ord x => DNF (SmartIndex x) -> DNF (SmartIndex x) ->
	DW x (DNF (SmartIndex x))
convertDNF start goal =
	finishConversion (startConversion start) goal >>=
	flip addUntil goal
