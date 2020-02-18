module Mapping (
    Mapping(..),
    BiMapping(..)
) where

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import qualified Data.Map.Merge.Lazy as Merge
import Control.Monad (join)

-- Union maps, keeping both values if they are equal, returning Nothing otherwise
union :: (Ord k, Eq v) => Map k v -> Map k v -> Maybe (Map k v)
union = Merge.mergeA
    Merge.preserveMissing
    Merge.preserveMissing
    (Merge.zipWithAMatched $ \_ x y -> if x==y then Just x else Nothing)

-- Map with monoid instance by union that might fail
newtype Mapping k v = Mapping
    { getMap :: Maybe (Map k v) }
    deriving (Show)

instance (Ord k, Eq v) => Semigroup (Mapping k v) where
    Mapping m1 <> Mapping m2 = Mapping $ join $ union <$> m1 <*> m2

instance (Ord k, Eq v) => Monoid (Mapping k v) where
    mempty = Mapping $ Just M.empty

-- Pair of maps with monoid instance by union that might fail
newtype BiMapping m x y = BiMapping
    { getMaps :: Maybe ( Map x (m y), Map y (m x) ) }
    deriving (Show)

instance (Ord x, Ord y, Eq (m x), Eq (m y)) => Semigroup (BiMapping m x y) where
    BiMapping (Just (f1,b1)) <> BiMapping (Just (f2,b2)) =
        BiMapping $ (,) <$> (mergeErr f1 f2) <*> (mergeErr b1 b2)
    _ <> _ = BiMapping Nothing

instance (Ord x, Ord y, Eq (m x), Eq (m y)) => Monoid (BiMapping m x y) where
    mempty = BiMapping $ Just (M.empty, M.empty)
