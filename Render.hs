{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Render (
	Renderable(..),
	putRender
) where

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.String (fromString)

-- Types with pretty rendering
class Renderable x where
	render :: x -> Text

instance Renderable Integer where
	render = fromString . show

instance Renderable Text where
	render = id

instance Renderable String where
	render = fromString

instance Renderable Bool where
	render = fromString . show

instance Renderable (Maybe Bool) where
	render (Just True) = "True"
	render Nothing = "Unknown"
	render (Just False) = "False"

instance (Renderable k, Renderable v) => Renderable (Map k v) where
	render m = T.unlines $
		zipWith formatCol rightKeys leftValues
		where
			formatCol k v = k <> " ↦ " <> v

			rendKeys = render <$> M.keys m
			lengthKeys = maximum $ T.length <$> rendKeys
			rightKeys = T.justifyRight lengthKeys ' ' <$> rendKeys

			leftValues = render <$> M.elems m

putRender :: Renderable x => x -> IO ()
putRender = TIO.putStr . render
