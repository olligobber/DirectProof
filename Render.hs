{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Render (
    Renderable(..),
    RenderableF(..),
    putRender,
    putRenders,
    putRenders2
) where

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.String (fromString)
import Data.Functor.Compose (Compose(..))

class Renderable x where
    render :: x -> Text

instance Renderable String where
    render = fromString

instance Renderable Bool where
    render = fromString . show

instance Renderable (Maybe Bool) where
    render (Just True) = "True"
    render Nothing = "Unknown"
    render (Just False) = "False"

putRender :: Renderable x => x -> IO ()
putRender = TIO.putStr . render

class RenderableF f where
    renders :: (x -> Text) -> f x -> Text

putRenders :: (RenderableF f, Renderable x) => f x -> IO ()
putRenders = TIO.putStr . renders render

instance (RenderableF f, RenderableF g) => RenderableF (Compose f g) where
    renders rend = renders (renders rend) . getCompose

class RenderableF2 f where
    renders2 :: (x -> Text) -> (y -> Text) -> f x y -> Text

putRenders2 :: (RenderableF2 f, Renderable x, Renderable y) => f x y -> IO ()
putRenders2 = TIO.putStr . renders2 render render

instance RenderableF2 Map where
    renders2 rendk rendv m = T.unlines $
        zipWith formatCol rightKeys leftValues
        where
            formatCol k v = k <> " ↦ " <> v

            rendKeys = rendk <$> M.keys m
            lengthKeys = maximum $ T.length <$> rendKeys
            rightKeys = T.justifyRight lengthKeys ' ' <$> rendKeys

            leftValues = rendv <$> M.elems m
