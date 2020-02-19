module Proof (
    Proof(..),
    mapWFF,
    compose
) where

import Data.Text (Text)

import Mapping (BiMapping(..))
import WFF (WFF)
import qualified WFF as W
import ReLabel (reLabel)

-- Very basic proof object
data Proof x = Proof {
    formulas :: [WFF x], -- List of formulas
    reasons :: [Text] -- List of reasons
}

mapWFF :: (WFF x -> WFF y) -> Proof x -> Proof y
mapWFF f p = Proof (f <$> formulas p) (reasons p)

instance Functor Proof where
    fmap f = mapWFF (fmap f)

instance Foldable Proof where
    foldMap f = foldMap (foldMap f) . formulas

instance Traversable Proof where
    sequenceA proof = Proof
        <$> (sequenceA $ fmap sequenceA $ formulas proof)
        <*> pure (reasons proof)

compose :: (Ord x, Ord y) => Proof x -> Proof y -> Proof (Either x y)
compose p1 p2 = case W.match p1end p2start of
    (BiMapping (Just (f,b))) -> Proof
        ( (W.applyMapLeft f <$> formulas p1)
            ++ tail (W.applyMapRight b <$> formulas p2) )
        ( reasons p1 ++ reasons p2 )
    _ -> error $ unlines
        [ "Failed to compose proofs, since the following formulas did not match:"
        , "    " ++ show (reLabel p1end :: WFF Integer)
        , "    " ++ show (reLabel p2start :: WFF Integer)
        ]
    where
        p1end = last $ formulas p1
        p2start = head $ formulas p2
