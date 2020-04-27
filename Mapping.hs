module Mapping (
	Mapping(..)
) where

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import qualified Data.Map.Merge.Lazy as Merge
import Control.Monad (join)

newtype Mapping k v = Mapping { getMap :: Maybe (Map k v) } deriving (Eq, Show)

instance (Ord k, Eq v) => Semigroup (Mapping k v) where
	Mapping m1 <> Mapping m2 = Mapping $ join $ mergeErr <$> m1 <*> m2 where
		mergeErr = Merge.mergeA
			Merge.preserveMissing
			Merge.preserveMissing
			(Merge.zipWithAMatched $ \_ x y -> if x==y then Just x else Nothing)

instance (Ord k, Eq v) => Monoid (Mapping k v) where
	mempty = Mapping $ Just M.empty
