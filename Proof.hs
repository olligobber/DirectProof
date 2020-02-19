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
    render
) where

import Data.Text (Text)
import qualified Data.Text as T

import Mapping (BiMapping(..))
import WFF (WFF)
import qualified WFF as W
import ReLabel (Labeling, reLabel, reLabelInt, single)

-- Very basic proof object
data Proof x = Proof {
    formulas :: [WFF x], -- List of formulas
    reasons :: [Text] -- List of reasons
}

identity :: WFF x -> Proof x
identity wff = Proof [wff] []

mapWFF :: (WFF x -> WFF y) -> Proof x -> Proof y
mapWFF f p = Proof (f <$> formulas p) (reasons p)

invert :: Proof x -> Proof x
invert p = Proof (reverse $ formulas p) (reverse $ reasons p)

liftLeft :: Labeling x => (forall y. WFF y -> WFF y -> WFF y) -> Proof x -> Proof x
liftLeft f p = reLabel $ mapWFF (flip f $ W.Prop $ Left single) $ Right <$> p

liftRight :: Labeling x => (forall y. WFF y -> WFF y -> WFF y) -> Proof x -> Proof x
liftRight f p = reLabel $ mapWFF (f $ W.Prop $ Left single) $ Right <$> p

-- Left to Right composition
compose :: (Ord x, Ord y) => Proof x -> Proof y -> Proof (Either x y)
compose p1 p2 = case W.match p1end p2start of
    (BiMapping (Just (f,b))) -> Proof
        ( (W.applyMapLeft f <$> formulas p1)
            ++ tail (W.applyMapRight b <$> formulas p2) )
        ( reasons p1 ++ reasons p2 )
    _ -> error $ unlines
        [ "Failed to compose proofs, since the following formulas did not match:"
        , "    " ++ show (reLabelInt p1end)
        , "    " ++ show (reLabelInt p2start)
        ]
    where
        p1end = last $ formulas p1
        p2start = head $ formulas p2

instance Functor Proof where
    fmap f = mapWFF (fmap f)

instance Foldable Proof where
    foldMap f = foldMap (foldMap f) . formulas

instance Traversable Proof where
    sequenceA proof = Proof
        <$> (sequenceA $ fmap sequenceA $ formulas proof)
        <*> pure (reasons proof)

instance (Ord x, Labeling x) => Semigroup (Proof x) where
    p1 <> p2 = reLabel $ compose p1 p2

instance (Ord x, Labeling x) => Monoid (Proof x) where
    mempty = Proof [W.Prop single] []

-- Nice rendering for the user
render :: (c -> Text) -> Proof c -> Text
render rend pf = T.unlines $
    zipWith (\x y -> T.unwords [x,"|",y]) rightFormulas leftReasons
    where
        rendFormulas = W.render rend <$> formulas pf
        lengthFormulas = maximum $ T.length <$> rendFormulas
        rightFormulas = T.justifyRight lengthFormulas ' ' <$> rendFormulas
        leftReasons = "Assumption" : reasons pf
