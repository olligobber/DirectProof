{-# LANGUAGE TypeOperators #-}

module DirectedProof (
    -- Types and conversions
    DirectedProof, toPlain, fromTyped, EquivProof, toDirected, fromIso, invert,
    render,
    -- Lifts
    liftAndLeft, liftAndRight, liftOrLeft, liftOrRight, liftImpliesLeft,
    liftImpliesRight, liftEquivLeft, liftEquivRight, liftNot
) where

import Data.Text (Text)

import TypedProof (type (|-)(), type (===)())
import qualified TypedProof as T
import Proof (Proof)
import qualified Proof as P
import ReLabel
import WFF (WFF(..))

newtype DirectedProof x = DirectedProof { toPlain :: Proof x }

instance Functor DirectedProof where
    fmap f = DirectedProof . fmap f . toPlain

instance Foldable DirectedProof where
    foldMap f = foldMap f . toPlain

instance Traversable DirectedProof where
    sequenceA = fmap DirectedProof . sequenceA . toPlain

instance (Ord x, Labeling x) => Semigroup (DirectedProof x) where
    (DirectedProof p1) <> (DirectedProof p2) = DirectedProof $ p1 <> p2

instance (Ord x, Labeling x) => Monoid (DirectedProof x) where
    mempty = DirectedProof mempty

fromTyped :: a |- b -> DirectedProof Integer
fromTyped = DirectedProof . T.toPlain

newtype EquivProof x = EquivProof { toDirected :: DirectedProof x }

instance Functor EquivProof where
    fmap f = EquivProof . fmap f . toDirected

instance Foldable EquivProof where
    foldMap f = foldMap f . toDirected

instance Traversable EquivProof where
    sequenceA = fmap EquivProof . sequenceA . toDirected

instance (Ord x, Labeling x) => Semigroup (EquivProof x) where
    (EquivProof p1) <> (EquivProof p2) = EquivProof $ p1 <> p2

instance (Ord x, Labeling x) => Monoid (EquivProof x) where
    mempty = EquivProof mempty

fromIso :: a === b -> EquivProof Integer
fromIso = EquivProof . fromTyped . T.toTyped

invert :: EquivProof x -> EquivProof x
invert = EquivProof . DirectedProof . P.invert . toPlain . toDirected

render :: (x -> Text) -> DirectedProof x -> Text
render rend (DirectedProof pf) = P.render rend pf

liftAndRight :: Labeling x => EquivProof x -> EquivProof x
liftAndRight (EquivProof (DirectedProof p)) = EquivProof $ DirectedProof $
    P.liftRight (:&:) p

liftAndLeft :: Labeling x => EquivProof x -> EquivProof x
liftAndLeft (EquivProof (DirectedProof p)) = EquivProof $ DirectedProof $
    P.liftLeft (:&:) p

liftOrRight :: Labeling x => EquivProof x -> EquivProof x
liftOrRight (EquivProof (DirectedProof p)) = EquivProof $ DirectedProof $
    P.liftRight (:|:) p

liftOrLeft :: Labeling x => EquivProof x -> EquivProof x
liftOrLeft (EquivProof (DirectedProof p)) = EquivProof $ DirectedProof $
    P.liftLeft (:|:) p

liftImpliesRight :: Labeling x => EquivProof x -> EquivProof x
liftImpliesRight (EquivProof (DirectedProof p)) = EquivProof $ DirectedProof $
    P.liftRight (:>:) p

liftImpliesLeft :: Labeling x => EquivProof x -> EquivProof x
liftImpliesLeft (EquivProof (DirectedProof p)) = EquivProof $ DirectedProof $
    P.liftLeft (:>:) p

liftEquivRight :: Labeling x => EquivProof x -> EquivProof x
liftEquivRight (EquivProof (DirectedProof p)) = EquivProof $ DirectedProof $
    P.liftRight (:=:) p

liftEquivLeft :: Labeling x => EquivProof x -> EquivProof x
liftEquivLeft (EquivProof (DirectedProof p)) = EquivProof $ DirectedProof $
    P.liftLeft (:=:) p

liftNot :: Labeling x => EquivProof x -> EquivProof x
liftNot (EquivProof (DirectedProof p)) = EquivProof $ DirectedProof $
    P.mapWFF Not p
