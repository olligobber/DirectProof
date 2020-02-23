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
    render,
    simpleRule,
    complexRule
) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.String (fromString)
import Data.Functor.Compose (Compose(..))

import WFF (WFF(..))
import qualified WFF as W
import ReLabel (Labeling, reLabel, reLabelInt, single, preserve)

-- Very basic proof object
data Proof x = Proof {
    formulas :: [WFF x], -- List of formulas
    reasons :: [Text], -- List of reasons
    references :: [[Int]] -- References for each reason, stored as relative indices
} deriving Show

identity :: WFF x -> Proof x
identity wff = Proof [wff] [] []

mapWFF :: (WFF x -> WFF y) -> Proof x -> Proof y
mapWFF f p = Proof (f <$> formulas p) (reasons p) (references p)

-- only works if the references are [-1,-1..]
invert :: Proof x -> Proof x
invert p
    | all (==[-1]) (references p) = Proof (rp formulas) (rp reasons) (references p)
    | otherwise = error "Cannot reverse proof as one of its rules is irreversible"
    where
        rp = reverse . ($ p)

liftLeft :: Labeling x => (forall y. WFF y -> WFF y -> WFF y) -> Proof x -> Proof x
liftLeft f p = reLabel $ mapWFF (flip f $ Prop $ Left single) $ Right <$> p

liftRight :: Labeling x => (forall y. WFF y -> WFF y -> WFF y) -> Proof x -> Proof x
liftRight f p = reLabel $ mapWFF (f $ Prop $ Left single) $ Right <$> p

-- Composition, using the function to prefer certain propositions
composePref :: (Ord x, Ord y) => (x -> Bool) -> (y -> Bool) ->
    Proof x -> Proof y -> Proof (Either x y)
composePref px py p1 p2 = case W.matchPref (either px py) p1end p2start of
    (Right m) -> Proof
        ( (W.applyMap m . fmap Left <$> formulas p1)
            ++ tail (W.applyMap m . fmap Right <$> formulas p2) )
        ( reasons p1 ++ reasons p2 )
        ( references p1 ++ references p2 )
    (Left (W.StructureError x y)) -> let
        [a,b,c,d] = getCompose $ reLabelInt $ Compose [p1end, p2start, x, y]
        in error $ unlines
            [ ""
            , "Failed to compose proofs, since the end of one did not match the"
            , "start of the other. The end of the first proof was"
            , "    " ++ show a
            , "and the start of the second was"
            , "    " ++ show b
            , "and when matching these, these two formulas could not be matched:"
            , "    " ++ show c
            , "    " ++ show d
            ]
    (Left (W.RecursionError p x)) -> let
        [a,b,Prop q,c] = getCompose $ reLabelInt $ Compose
            [p1end, p2start, Prop p, x]
        in error $ unlines
            [ ""
            , "Failed to compose proofs, since the end of one did not match the"
            , "start of the other. The end of the first proof was"
            , "    " ++ show a
            , "and the start of the second was"
            , "    " ++ show b
            , "and when matching these, an infinite formula was created:"
            , "    " ++ show q ++ " := " ++ show c
            ]
    where
        p1end = Left <$> last (formulas p1)
        p2start = Right <$> head (formulas p2)

-- Left to Right composition
compose :: (Ord x, Ord y) => Proof x -> Proof y -> Proof (Either x y)
compose = composePref (const False) (const False)

instance Functor Proof where
    fmap f = mapWFF (fmap f)

instance Foldable Proof where
    foldMap f = foldMap (foldMap f) . formulas

instance Traversable Proof where
    sequenceA proof = Proof
        <$> (sequenceA $ fmap sequenceA $ formulas proof)
        <*> pure (reasons proof)
        <*> pure (references proof)

instance (Ord x, Labeling x) => Semigroup (Proof x) where
    p1 <> p2 = reLabel $ composePref preserve preserve p1 p2

instance (Ord x, Labeling x) => Monoid (Proof x) where
    mempty = identity $ Prop single

-- Nice rendering for the user
render :: (c -> Text) -> Proof c -> Text
render rend pf = T.unlines $
    zipWith3 formatCol rightNumbers midFormulas leftReasons
    where
        formatCol n f r = T.intercalate " | " [n,f,r]
        fullLength = length $ formulas pf

        numbers = fromString . show <$> [1..fullLength]
        lengthNumbers = maximum $ T.length <$> numbers
        rightNumbers = T.justifyRight lengthNumbers ' ' <$> numbers

        rendFormulas = W.render rend <$> formulas pf
        lengthFormulas = maximum $ T.length <$> rendFormulas
        midFormulas = T.center lengthFormulas ' ' <$> rendFormulas

        showReferences fs n = T.intercalate "," $ fromString . show . (+ n) <$> fs
        fullReferences = zipWith showReferences (references pf) [2..]
        leftReasons = "Assumption" :
            zipWith (\x y -> T.unwords [x,y]) (reasons pf) fullReferences

-- Create a proof that applies a rule to one formula to get another
simpleRule :: WFF x -> WFF x -> Text -> Proof x
simpleRule start end reason = Proof [start, end] [reason] [[-1]]

{-
    Create a proof that applies a rule that combines two formulas from the end
    of two proofs that start with the same formula
-}
complexRule :: (Ord x, Labeling x) => WFF x -> WFF x -> WFF x -> Text ->
    Proof x -> Proof x -> Proof x
complexRule in1 in2 out reason pf1 pf2
    | length1 == 0 && length2 == 0 = Proof
        ( formulas1 ++ [final] )
        [reason]
        [[-1,-1]]
    | length1 == 0 = Proof
        ( formulas2 ++ [final] )
        ( reasons pf2 ++ [reason] )
        ( references pf2 ++ [[-1-length2, -1]] )
    | length2 == 0 = Proof
        ( formulas1 ++ [final] )
        ( reasons pf1 ++ [reason] )
        ( references pf1 ++ [[-1-length1, -1]] )
    | otherwise = Proof
        ( formulas1 ++ tail formulas2 ++ [final] )
        ( reasons pf1 ++ reasons pf2 ++ [reason] )
        ( concat
            [ references pf1
            , [(\x -> x - length1) <$> head (references pf2)]
            , tail $ references pf2
            , [[-1-length2, -1]]
            ] )
    where
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
                    , "    " ++ show a
                    , "    " ++ show b
                    , "and when matching these, these two formulas could not be"
                    , "matched:"
                    , "    " ++ show c
                    , "    " ++ show d
                    ]
            Left (W.RecursionError p x) -> let
                [a,b,Prop q,c] = getCompose $ reLabelInt $ Compose
                    [start1, start2, Prop p, x]
                in error $ unlines
                    [ ""
                    , "Failed to merge proofs, since the start of one did not"
                    , "match the start of the other. The starts where"
                    , "    " ++ show a
                    , "    " ++ show b
                    , "and when matching these, an infinite formula was created:"
                    , "    " ++ show q ++ " := " ++ show c
                    ]
        [formulas1', formulas2'] =
            fmap getCompose $ getCompose $ reLabel $ Compose $ fmap Compose
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
                    , "    " ++ show a
                    , "and the input to the rule was"
                    , "    " ++ show b
                    , "and when matching these, these two formulas could not be"
                    , "matched:"
                    , "    " ++ show c
                    , "    " ++ show d
                    ]
            Left (W.RecursionError p x) -> let
                [a,b,Prop q,c] = getCompose $ reLabelInt $ Compose
                    [end, inn, Prop p, x]
                in error $ unlines
                    [ ""
                    , "Failed to apply rule, since the end of the proofs did not"
                    , "match the input to the rule. The end was"
                    , "    " ++ show a
                    , "and the input to the rule was"
                    , "    " ++ show b
                    , "and when matching these, an infinite formula was created:"
                    , "    " ++ show q ++ " := " ++ show c
                    ]
        [formulas1, formulas2, [final]] =
            fmap getCompose $ getCompose $ reLabel $ Compose $ fmap Compose
                [ W.applyMap m2 . fmap Left <$> formulas1'
                , W.applyMap m2 . fmap Left <$> formulas2'
                , [W.applyMap m2 $ fmap Right out]
                ]
        length1 = length $ reasons pf1
        length2 = length $ reasons pf2
