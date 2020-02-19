{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ReLabel (
    ReLabel(..),
    reLabel,
    SmartIndex(..)
) where

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import qualified Control.Monad.State as S

-- Types that support relabelling one type to another in data structures
class ReLabel x y where
    data family State x y :: *
    -- Start state of relabelling
    start :: State x y
    -- Relabel one element, updating the state
    reLabelOne :: x -> State x y -> (y, State x y)

-- Relabel all elements of a structure
reLabel :: (ReLabel x y, Traversable t) => t x -> t y
reLabel struct = S.evalState (traverse (S.state . reLabelOne) struct) start

-- Relabel with 1,2..
instance Ord x => ReLabel x Integer where
    data State x Integer = StateInteger {
        nextInt :: Integer,
        usedInt :: Map x Integer
    }
    start = StateInteger 1 M.empty
    reLabelOne oldLabel state = case M.lookup oldLabel $ usedInt state of
        Just newLabel -> (newLabel, state)
        Nothing -> ( nextInt state,
            StateInteger
                (nextInt state + 1)
                (M.insert oldLabel (nextInt state) $ usedInt state)
            )

-- Either a value or an index that will be relabelled properly
data SmartIndex x = Index Integer | Value x deriving (Eq, Ord, Show)

instance Functor SmartIndex where
    fmap _ (Index i) = Index i
    fmap f (Value x) = Value $ f x

type Two x = Either x x

-- Relabel disjoint union of smart indices, keeping values and relabelling indices with 1,2...
instance Ord x => ReLabel (Two (SmartIndex x)) (SmartIndex x) where
    data State (Two (SmartIndex x)) (SmartIndex x) = StateSmart {
        nextSmart :: Integer,
        usedSmart :: Map (Either Integer Integer) Integer
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
