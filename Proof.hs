{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}

module Proof (
	Proof(..),
	mapWFF,
	compose,
	identity,
	invert,
	liftLeft,
	liftRight,
	algebraicRule,
	equivalenceRule,
	simpleRule,
	complexRule,
	verify
) where

import qualified Data.Text as T
import Data.String (fromString)
import Data.Functor.Compose (Compose(..))
import Control.Monad.State (StateT)
import qualified Control.Monad.State as S
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M

import WFF (WFF(..), BinaryOperator)
import qualified WFF as W
import ReLabel (Labeling, reLabel, reLabelInt, single, preserve)
import Render (Renderable(..))
import Deduction

-- Very basic proof object
data Proof x = Proof {
	-- List of formulas
	formulas :: [WFF x],
	-- List of reasons for each deduction, except the first
	reasons :: [Deduction]
} deriving (Show, Eq)

-- Empty proof
identity :: WFF x -> Proof x
identity wff = Proof [wff] []

-- Apply a function to all WFFs of a proof
mapWFF :: (WFF x -> WFF y) -> Proof x -> Proof y
mapWFF f p = Proof (f <$> formulas p) (reasons p)

-- Reverses a proof, only works if the references are all to previous line
invert :: Proof x -> Proof x
invert p
	| all invertible (reasons p) =
		Proof (rp formulas) (rp reasons)
	| otherwise =
		error "Cannot reverse proof as one of its rules is irreversible"
	where
		rp = reverse . ($ p)

-- Apply a proof to left subformula
liftLeft :: Labeling x => BinaryOperator -> Proof x -> Proof x
liftLeft f p = reLabel $ mapWFF (flip f $ Prop $ Left single) $ Right <$> p

-- Apply a proof to right subformula
liftRight :: Labeling x => BinaryOperator -> Proof x -> Proof x
liftRight f p = reLabel $ mapWFF (f $ Prop $ Left single) $ Right <$> p

{-
	Left to right composition, using the given function to prefer keeping
	certain propositions
-}
composePref :: (Ord x, Ord y) => (x -> Bool) -> (y -> Bool) ->
	Proof x -> Proof y -> Proof (Either x y)
composePref px py p1 p2 = case W.matchPref (either px py) p1end p2start of
	(Right m) -> Proof
		( (W.applyMap m . fmap Left <$> formulas p1)
			++ tail (W.applyMap m . fmap Right <$> formulas p2) )
		( reasons p1 ++ reasons p2 )
	(Left (W.StructureError x y)) -> let
		[a,b,c,d] = getCompose $ reLabelInt $ Compose [p1end, p2start, x, y]
		in error $ unlines
			[ ""
			, "Failed to compose proofs, since the end of one did not match the"
			, "start of the other. The end of the first proof was"
			, "\t" ++ show a
			, "and the start of the second was"
			, "\t" ++ show b
			, "and when matching these, these two formulas could not be matched:"
			, "\t" ++ show c
			, "\t" ++ show d
			]
	(Left (W.RecursionError p x)) -> let
		[a,b,Prop q,c] = getCompose $ reLabelInt $ Compose
			[p1end, p2start, Prop p, x]
		in error $ unlines
			[ ""
			, "Failed to compose proofs, since the end of one did not match the"
			, "start of the other. The end of the first proof was"
			, "\t" ++ show a
			, "and the start of the second was"
			, "\t" ++ show b
			, "and when matching these, an infinite formula was created:"
			, "\t" ++ show q ++ " := " ++ show c
			]
	where
		p1end = Left <$> last (formulas p1)
		p2start = Right <$> head (formulas p2)

{-
	Left to Right composition of proofs, with no preference on propositions to
	keep
-}
compose :: (Ord x, Ord y) => Proof x -> Proof y -> Proof (Either x y)
compose = composePref (const False) (const False)

-- Traversable functor on propositions
instance Functor Proof where
	fmap f = mapWFF (fmap f)

instance Foldable Proof where
	foldMap f = foldMap (foldMap f) . formulas

instance Traversable Proof where
	sequenceA proof = Proof
		<$> traverse sequenceA (formulas proof)
		<*> pure (reasons proof)

-- Monoid on left to right composition
instance (Ord x, Labeling x) => Semigroup (Proof x) where
	p1 <> p2 = reLabel $ composePref preserve preserve p1 p2

instance (Ord x, Labeling x) => Monoid (Proof x) where
	mempty = identity $ Prop single

-- Pretty rendering
instance Renderable x => Renderable (Proof x) where
	render pf = T.unlines $
		zipWith3 formatCol rightNumbers midFormulas leftReasons
		where
			formatCol n f r = T.intercalate " | " [n,f,r]
			fullLength = length $ formulas pf

			numbers = fromString . show <$> [1..fullLength]
			lengthNumbers = maximum $ T.length <$> numbers
			rightNumbers = T.justifyRight lengthNumbers ' ' <$> numbers

			rendFormulas = render <$> formulas pf
			lengthFormulas = maximum $ T.length <$> rendFormulas
			midFormulas = T.center lengthFormulas ' ' <$> rendFormulas

			leftReasons = zipWith renderDeduction (Assumption:reasons pf) [1..]

-- Create a proof that applies an algebraic rule
algebraicRule ::
	AlgebraicRule -> BinaryOperator -> BinaryOperator -> Proof Integer
algebraicRule rule op1 op2 = Proof [start, end] [Algebraic rule 1] where
	(start,end) = makeEquivs rule op1 op2

-- Create a proof that applies an equivalence rule
equivalenceRule :: EquivRule -> Proof Integer
equivalenceRule rule = Proof [start, end] [Equiv rule 1] where
	(start, end) = getEquivs rule

-- Create a proof that applies a simple rule
simpleRule :: SimpleRule -> Proof Integer
simpleRule rule = Proof [start, end] [Simple rule 1] where
	(start, end) = getImplies rule

{-
	Create a proof that applies a complex rule using the end
	of two proofs that start with the same formula
-}
complexRule :: ComplexRule -> Proof Integer -> Proof Integer -> Proof Integer
complexRule rule pf1 pf2
	| length1 == 0 && length2 == 0 = Proof
		( formulas1 ++ [final] )
		[Complex rule 1 1]
	| length1 == 0 = Proof
		( formulas2 ++ [final] )
		( reasons pf2 ++ [Complex rule 1 (1+length2)] )
	| length2 == 0 = Proof
		( formulas1 ++ [final] )
		( reasons pf1 ++ [Complex rule (1+length1) 1] )
	| otherwise = Proof
		( formulas1 ++ tail formulas2 ++ [final] )
		( concat
			[ reasons pf1
			, zipWith (changeRef length1) (reasons pf2) [1..]
			, [Complex rule (length2 + 1) 1]
			] )
	where
		(in1, in2, out) = getParts rule
		start1 = Left <$> head (formulas pf1)
		start2 = Right <$> head (formulas pf2)
		m1 = case W.matchPref (either preserve preserve) start1 start2 of
			Right m -> m
			Left (W.StructureError x y) -> let
				[a,b,c,d] = getCompose $ reLabelInt $ Compose
					[start1, start2, x, y]
				in error $ unlines
					[ ""
					, "Failed to merge proofs, since the start of one did not"
					, "match the start of the other. The starts where"
					, "\t" ++ show a
					, "\t" ++ show b
					, "and when matching these, these two formulas could not be"
					, "matched:"
					, "\t" ++ show c
					, "\t" ++ show d
					]
			Left (W.RecursionError p x) -> let
				[a,b,Prop q,c] = getCompose $ reLabelInt $ Compose
					[start1, start2, Prop p, x]
				in error $ unlines
					[ ""
					, "Failed to merge proofs, since the start of one did not"
					, "match the start of the other. The starts where"
					, "\t" ++ show a
					, "\t" ++ show b
					, "and when matching these, an infinite formula was created:"
					, "\t" ++ show q ++ " := " ++ show c
					]
		[formulas1', formulas2'] =
			getCompose $ getCompose $ reLabel $ Compose $ Compose
				[ W.applyMap m1 . fmap Left <$> formulas pf1
				, W.applyMap m1 . fmap Right <$> formulas pf2
				]
		end = Left <$> last formulas1' :&: last formulas2'
		inn = Right <$> in1 :&: in2
		m2 = case W.matchPref (either preserve preserve) end inn of
			Right m -> m
			Left (W.StructureError x y) -> let
				[a,b,c,d] = getCompose $ reLabelInt $ Compose
					[end, inn, x, y]
				in error $ unlines
					[ ""
					, "Failed to apply rule, since the end of the proofs did not"
					, "match the input to the rule. The end was"
					, "\t" ++ show a
					, "and the input to the rule was"
					, "\t" ++ show b
					, "and when matching these, these two formulas could not be"
					, "matched:"
					, "\t" ++ show c
					, "\t" ++ show d
					]
			Left (W.RecursionError p x) -> let
				[a,b,Prop q,c] = getCompose $ reLabelInt $ Compose
					[end, inn, Prop p, x]
				in error $ unlines
					[ ""
					, "Failed to apply rule, since the end of the proofs did not"
					, "match the input to the rule. The end was"
					, "\t" ++ show a
					, "and the input to the rule was"
					, "\t" ++ show b
					, "and when matching these, an infinite formula was created:"
					, "\t" ++ show q ++ " := " ++ show c
					]
		[formulas1, formulas2, [final]] =
			getCompose $ getCompose $ reLabel $ Compose $ Compose
				[ W.applyMap m2 . fmap Left <$> formulas1'
				, W.applyMap m2 . fmap Left <$> formulas2'
				, [W.applyMap m2 $ fmap Right out]
				]
		length1 = toInteger $ length $ reasons pf1
		length2 = toInteger $ length $ reasons pf2

type Verification x = StateT (Map Integer (WFF x)) (Either Integer)

verifyS :: Ord x => (Integer, WFF x, Deduction) -> Verification x ()
verifyS (l, formula, Assumption) = S.modify $ M.insert l formula
verifyS (l, formula, Algebraic rule i) = do
	ref <- S.gets $ M.lookup (l-i)
	case ref of
		Just refs | verifyAlg rule refs formula ->
			S.modify $ M.insert l formula
		_ -> S.StateT $ const $ Left l
verifyS (l, formula, Equiv rule i) = do
	ref <- S.gets $ M.lookup (l-i)
	case ref of
		Just refs | verifyEquivs rule refs formula ->
			S.modify $ M.insert l formula
		_ -> S.StateT $ const $ Left l
verifyS (l, formula, Simple rule i) = do
	ref <- S.gets $ M.lookup (l-i)
	case ref of
		Just refs | verifySimple rule refs formula ->
			S.modify $ M.insert l formula
		_ -> S.StateT $ const $ Left l
verifyS (l, formula, Complex rule i j) = do
	refi <- S.gets $ M.lookup (l-i)
	refj <- S.gets $ M.lookup (l-j)
	case (refi, refj) of
		(Just refsi, Just refsj) | verifyComplex rule refsi refsj formula ->
			S.modify $ M.insert l formula
		_ -> S.StateT $ const $ Left l

verify :: Ord x => Proof x -> Maybe Integer
verify pf = case flip S.evalStateT M.empty $ mapM_ verifyS $
	zip3 [1..] (formulas pf) (Assumption:reasons pf) of
		Left l -> Just l
		Right _ -> Nothing
