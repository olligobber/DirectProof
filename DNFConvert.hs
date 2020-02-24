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
import Control.Monad (foldM)

import DNF
import WFFType
import DirectedProof (DirectedProof, EquivProof)
import qualified DirectedProof as D
import TypedProof (type (|~)(), type (|-)())
import qualified TypedProof as T
import ReLabel (SmartIndex(..))

-- Represents a partly done conversion, with the formula (inP | (conv | unconv))
-- If one is missing, form is (a | b)
-- If two are missing, form is a
-- Three should never be missing
data DNFConversion x = DNFConversion {
    inProgress :: Maybe (Clause (SmartIndex x)),
    converted :: Maybe (DNF (SmartIndex x)),
    unconverted :: Maybe (DNF (SmartIndex x))
}

-- Start the conversion process of a DNF
startConversion :: DNF (SmartIndex x) -> DNFConversion x
startConversion dnf = DNFConversion
    (Just $ head $ clauses dnf)
    Nothing
    (pop dnf)

-- Move inProgress to converted and get something from unconverted to progress on
nextProgress :: Ord x => DNFConversion x ->
    EW x (Either (DNF (SmartIndex x)) (DNFConversion x))
nextProgress (DNFConversion Nothing Nothing (Just uncon)) =
    return $ Right $ DNFConversion
        (Just $ head $ clauses uncon)
        Nothing
        (pop uncon)
nextProgress (DNFConversion Nothing (Just conv) Nothing) =
    return $ Left conv
nextProgress (DNFConversion (Just c) Nothing Nothing) =
    return $ Left $ singleton c
nextProgress (DNFConversion (Just c) (Just conv) Nothing) =
    Left <$> insertClause c conv
nextProgress (DNFConversion (Just c) Nothing (Just uncon)) =
    case clauses uncon of
        [unc] -> do
            W.tell $ Index <$> D.fromIso (T.commutationOr :: a \/ b |~ b \/ a)
            return $ Right $ DNFConversion
                (Just unc)
                (Just $ singleton c)
                Nothing
        unc:_ -> do
            W.tell $ Index <$> D.fromIso (
                T.associationOr >>>
                T.liftOrLeft T.commutationOr >>>
                T.invert T.associationOr
                :: a \/ (b \/ c) |~ b \/ (a \/ c)
                )
            return $ Right $ DNFConversion
                (Just unc)
                (Just $ singleton c)
                (pop uncon)
nextProgress (DNFConversion (Just c) (Just conv) (Just uncon)) =
    case clauses uncon of
        [unc] -> do
            W.tell $ Index <$> D.fromIso (
                T.associationOr >>>
                T.commutationOr
                :: a \/ (b \/ c) |~ c \/ (a \/ b)
                )
            nconv <- W.censor D.liftOrRight $ insertClause c conv
            return $ Right $ DNFConversion (Just unc) (Just nconv) Nothing
        unc:_ -> do
            W.tell $ Index <$> D.fromIso (
                T.liftOrRight
                    (T.liftOrRight T.commutationOr >>> T.associationOr) >>>
                T.associationOr >>>
                T.commutationOr >>>
                T.liftOrRight T.associationOr
                :: a \/ (b \/ (c \/ d)) |~ c \/ ((a \/ b) \/ d)
                )
            nconv <- W.censor (D.liftOrRight . D.liftOrLeft) $
                insertClause c conv
            return $ Right $ DNFConversion (Just unc) (Just nconv) (pop uncon)

-- Check if a clause contains two opposite atoms and return the proposition
getContradiction :: Eq x => Clause x -> Maybe x
getContradiction clause = case
    filter ((==2) . length) $ groupBy ((==) `on` fst) $ atoms clause of
        [] -> Nothing
        ((p,_):_):_ -> Just p

-- Check if the second is a subclause of the first
isSubClause :: Eq x => Clause x -> Clause x -> Bool
isSubClause = flip (isSubsequenceOf `on` atoms)

-- Find the longest subclause from a DNF
bestSubClause :: Eq x => Clause x -> DNF x -> Maybe (Clause x)
bestSubClause clause dnf = case filter (isSubClause clause) $ clauses dnf of
    [] -> Nothing
    cs -> Just $ maximumBy (compare `on` length . atoms) cs

-- Update inProgress, given the goal dnf
makeProgress :: Ord x => DNF (SmartIndex x) -> DNFConversion x ->
    DW x (DNFConversion x)
makeProgress _ dnfc@(DNFConversion Nothing _ _) = return dnfc
makeProgress goal (DNFConversion (Just inP) Nothing Nothing) =
    case bestSubClause inP goal of
        Nothing -> error "Unable to convert DNF"
        Just c -> do
            ninP <- removeAtomsAlone (atoms inP \\ atoms c) inP
            return $ DNFConversion (Just ninP) Nothing Nothing
makeProgress goal (DNFConversion (Just inP) conv unconv) =
    case (getContradiction inP, bestSubClause inP goal) of
        (Nothing, Nothing) -> error "Unable to convert DNF"
        (_, Just c) -> do
            -- This case is first so we don't delete everything useful
            ninP <- removeAtoms (atoms inP \\ atoms c) inP
            return $ DNFConversion (Just ninP) conv unconv
        (Just p, _) -> do
            ninP <- removeAtoms (takeWhile ((/= p) . fst) $ atoms inP) inP
            if length (atoms ninP) == 2 then
                W.tell $ Index <$> (D.toDirected . D.fromIso) (
                    T.commutationOr >>>
                    T.distribution2
                    :: (a /\ Not a) \/ b |~ (b \/ a) /\ (b \/ Not a)
                    )
            else
                W.tell $ Index <$> D.fromTyped (
                    T.toTyped (
                        T.commutationOr >>>
                        T.distribution2 >>>
                        T.liftAndRight T.distribution2 >>>
                        T.associationAnd
                        ) >>>
                    T.simplification
                    :: (a /\ (Not a /\ b)) \/ c |- (c \/ a) /\ (c \/ Not a)
                    )
            W.tell $ Index <$> D.fromTyped (
                T.toTyped (
                    T.liftAndLeft (
                        T.liftOrLeft T.doubleNegation >>>
                        T.invert T.defImplication
                        ) >>>
                    T.liftAndRight (
                        T.commutationOr >>>
                        T.invert T.defImplication
                        )
                    ) >>>
                T.hypotheticalS
                    (T.simplification)
                    (T.toTyped T.commutationAnd >>> T.simplification)
                >>>
                T.toTyped (
                    T.defImplication >>>
                    T.liftOrLeft (T.invert T.doubleNegation) >>>
                    T.invert T.idempotenceOr
                    )
                :: (b \/ a) /\ (b \/ Not a) |- b
                )
            return $ DNFConversion Nothing conv unconv

finishConversion :: Ord x => DNFConversion x -> DNF (SmartIndex x) ->
    DW x (DNF (SmartIndex x))
finishConversion dnfc goal = do
    next <- makeProgress goal dnfc >>= toDW . nextProgress
    case next of
        Left dnf -> return dnf
        Right nextdnfc -> finishConversion nextdnfc goal

-- Adds the given clause to a dnf
addClause :: Ord x => DNF (SmartIndex x) -> Clause (SmartIndex x) ->
    DW x (DNF (SmartIndex x))
addClause dnf clause = do
    W.tell $ Index <$> D.fromTyped (
        T.addition >>>
        T.toTyped T.commutationOr
        :: a |- b \/ a
        )
    toDW $ insertClause clause dnf

-- Adds clauses to the first dnf until it matches the second
addUntil :: Ord x => DNF (SmartIndex x) -> DNF (SmartIndex x) ->
    DW x (DNF (SmartIndex x))
addUntil start goal = foldM addClause start $ clauses goal \\ clauses start

convertDNF :: Ord x => DNF (SmartIndex x) -> DNF (SmartIndex x) ->
    DW x (DNF (SmartIndex x))
convertDNF start goal =
    finishConversion (startConversion start) goal >>=
    addUntil goal
