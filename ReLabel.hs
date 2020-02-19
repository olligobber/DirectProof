{-# LANGUAGE TypeFamilies #-}

module ReLabel (
    reLabelInt,
    Two,
    Labeling(..),
    reLabel,
    SmartIndex(..)
) where

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import qualified Control.Monad.State as S

-- Relabel with 1,2..
reLabelInt :: (Ord x, Traversable t) => t x -> t Integer
reLabelInt struct = S.evalState (traverse (S.state . onOne) struct) start where
    start = (1, M.empty)
    onOne oldLabel (nextLabel, used) = case M.lookup oldLabel used of
        Nothing -> (nextLabel, (nextLabel + 1, M.insert oldLabel nextLabel used))
        Just newLabel -> (newLabel, (nextLabel, used))

type Two x = Either x x

-- Types that support relabelling a disjoint union in a structure
class Labeling x where
    data family State x :: *
    -- Start state of relabelling
    start :: State x
    -- Relabel one element, updating the state
    reLabelOne :: Two x -> State x -> (x, State x)
    -- A single label to be used when one extra is needed
    single :: x

-- Relabel all elements of a structure
reLabel :: (Labeling x, Traversable t) => t (Two x) -> t x
reLabel struct = S.evalState (traverse (S.state . reLabelOne) struct) start

-- Relabel with 1,2..
instance Labeling Integer where
    data State Integer = StateInteger {
        nextInt :: Integer,
        usedInt :: Map (Two Integer) Integer
    }
    start = StateInteger 1 M.empty
    reLabelOne oldLabel state = case M.lookup oldLabel $ usedInt state of
        Just newLabel -> (newLabel, state)
        Nothing -> ( nextInt state,
            StateInteger
                (nextInt state + 1)
                (M.insert oldLabel (nextInt state) $ usedInt state)
            )
    single = 1

-- Either a value or an index that will be relabelled properly
data SmartIndex x = Index Integer | Value x deriving (Eq, Ord, Show)

instance Functor SmartIndex where
    fmap _ (Index i) = Index i
    fmap f (Value x) = Value $ f x

-- Keeping values and relabel indices with 1,2...
instance Labeling (SmartIndex x) where
    data State (SmartIndex x) = StateSmart {
        nextSmart :: Integer,
        usedSmart :: Map (Two Integer) Integer
    }
    start = StateSmart 1 M.empty
    reLabelOne (Left (Value label)) state = (Value label, state)
    reLabelOne (Right (Value label)) state = (Value label, state)
    reLabelOne (Left (Index oldLabel)) state =
        case M.lookup (Left oldLabel) $ usedSmart state of
            Just newLabel -> (Index newLabel, state)
            Nothing -> (Index $ nextSmart state,
                StateSmart
                    (nextSmart state + 1)
                    (M.insert (Left oldLabel) (nextSmart state) $ usedSmart state)
                )
    reLabelOne (Right (Index oldLabel)) state =
        case M.lookup (Right oldLabel) $ usedSmart state of
            Just newLabel -> (Index newLabel, state)
            Nothing -> (Index $ nextSmart state,
                StateSmart
                    (nextSmart state + 1)
                    (M.insert (Right oldLabel) (nextSmart state) $ usedSmart state)
                )
    single = Index 1
