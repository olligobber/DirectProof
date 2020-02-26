{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module DirectedProof (
    -- Types and conversions
    DirectedProof, toPlain, fromTyped, EquivProof, toDirected, fromIso, invert,
    identity, assumptions,
    -- Lifts
    liftAndLeft, liftAndRight, liftOrLeft, liftOrRight, liftImpliesLeft,
    liftImpliesRight, liftEquivLeft, liftEquivRight, liftNot
) where

import TypedProof (type (|-)(), type (|~)())
import qualified TypedProof as T
import Proof (Proof)
import qualified Proof as P
import ReLabel (Labeling)
import WFF (WFF(..))
import Render (RenderableF(..))

newtype DirectedProof x = DirectedProof { toPlain :: Proof x }
    deriving (Show, Eq)

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

instance RenderableF DirectedProof where
    renders rend = renders rend . toPlain

fromTyped :: a |- b -> DirectedProof Integer
fromTyped = DirectedProof . T.toPlain

newtype EquivProof x = EquivProof { toDirected :: DirectedProof x }
    deriving Show

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

instance RenderableF EquivProof where
    renders rend = renders rend . toDirected

identity :: WFF x -> EquivProof x
identity = EquivProof . DirectedProof . P.identity

fromIso :: a |~ b -> EquivProof Integer
fromIso = EquivProof . fromTyped . T.toTyped

invert :: EquivProof x -> EquivProof x
invert = EquivProof . DirectedProof . P.invert . toPlain . toDirected

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

-- Convert assumptions to a single formula
assumptions :: [WFF x] -> (DirectedProof x, WFF x)
assumptions [] = error "Cannot have a proof with no assumptions"
assumptions [a] = (DirectedProof $ P.identity a, a)
assumptions (a:as) = (
    DirectedProof $ P.Proof nformulas nreasons nreferences,
    a :&: nas ) where
        (DirectedProof (P.Proof oformulas oreasons oreferences), nas) =
            assumptions as
        nformulas = oformulas ++ [a, a :&: nas]
        nreasons = oreasons ++ ["Assumption", "Conjunction"]
        nreferences = oreferences ++ [[], [(-2),(-1)]]
