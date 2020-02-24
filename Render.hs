{-# LANGUAGE FlexibleInstances #-}

module Render (
    Renderable(..),
    RenderableF(..),
    putRender,
    putRenders
) where

import Data.Text (Text)
import qualified Data.Text.IO as TIO
import Data.String (fromString)
import Data.Functor.Compose (Compose(..))

class Renderable x where
    render :: x -> Text

instance Renderable String where
    render = fromString

class RenderableF f where
    renders :: (x -> Text) -> f x -> Text

putRender :: Renderable x => x -> IO ()
putRender = TIO.putStr . render

putRenders :: (RenderableF f, Renderable x) => f x -> IO ()
putRenders = TIO.putStr . renders render

instance (RenderableF f, RenderableF g) => RenderableF (Compose f g) where
    renders rend = renders (renders rend) . getCompose
