{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ReLabel (
    reLabelInt,
    Labeling(..),
    SmartIndex(..)
) where

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import qualified Control.Monad.State as S
import Data.String (fromString)

import Render (Renderable(..))

-- Relabel with 1,2..
reLabelInt :: (Ord x, Traversable t) => t x -> t Integer
reLabelInt struct = S.evalState (traverse (S.state . onOne) struct) startI where
    startI = (1, M.empty)
    onOne oldLabel (nextLabel, usedL) = case M.lookup oldLabel usedL of
        Nothing -> (nextLabel, (nextLabel + 1, M.insert oldLabel nextLabel usedL))
        Just newLabel -> (newLabel, (nextLabel, usedL))

-- Types that support relabelling a disjoint union in a structure
class Labeling x where

    type family State x :: *
    type State x = [Either x x]

    -- Start state of relabelling
    start :: State x
    default start :: State x ~ [Either x x] => State x
    start = []

    -- Relabel one element, updating the state
    reLabelOne :: Either x x -> State x -> (x, State x)
    default reLabelOne :: State x ~ [Either x x] =>
        Either x x -> State x -> (x, State x)
    reLabelOne x xs = (last $ reLabel $ xs ++ [x], xs ++ [x])

    -- Relabel an entire structure
    reLabel :: Traversable t => t (Either x x) -> t x
    reLabel struct =
        S.evalState (traverse (S.state . (reLabelOne @x)) struct) (start @x)

    -- A single label to be used when one extra is needed
    single :: x
    -- Labels that should be preserved over others
    preserve :: x -> Bool
    preserve = const False

    {- MINIMAL ((State, start, reLabelOne) | reLabel), single -}

data StateInteger = StateInteger {
    next :: Integer,
    used :: Map (Either Integer Integer) Integer
}

-- Relabel with 1,2..
instance Labeling Integer where
    type State Integer = StateInteger
    start = StateInteger 1 M.empty
    reLabelOne oldLabel state = case M.lookup oldLabel $ used state of
        Just newLabel -> (newLabel, state)
        Nothing -> ( next state,
            StateInteger
                (next state + 1)
                (M.insert oldLabel (next state) $ used state)
            )
    single = 1
    preserve = const False

-- Either a value or an index that will be relabelled properly
data SmartIndex x = Value x | Index Integer deriving (Eq, Ord, Show)

instance Renderable x => Renderable (SmartIndex x) where
    render (Index i) = "t_" <> fromString (show i)
    render (Value v) = render v

instance Functor SmartIndex where
    fmap _ (Index i) = Index i
    fmap f (Value x) = Value $ f x

-- Keeping values and relabel indices with 1,2...
instance Labeling (SmartIndex x) where
    type State (SmartIndex x) = StateInteger
    start = StateInteger 1 M.empty
    reLabelOne (Left (Value label)) state = (Value label, state)
    reLabelOne (Right (Value label)) state = (Value label, state)
    reLabelOne (Left (Index oldLabel)) state =
        case M.lookup (Left oldLabel) $ used state of
            Just newLabel -> (Index newLabel, state)
            Nothing -> (Index $ next state,
                StateInteger
                    (next state + 1)
                    (M.insert (Left oldLabel) (next state) $ used state)
                )
    reLabelOne (Right (Index oldLabel)) state =
        case M.lookup (Right oldLabel) $ used state of
            Just newLabel -> (Index newLabel, state)
            Nothing -> (Index $ next state,
                StateInteger
                    (next state + 1)
                    (M.insert (Right oldLabel) (next state) $ used state)
                )
    single = Index 1
    preserve (Index _) = False
    preserve (Value _) = True
