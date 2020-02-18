module WFF(
    WFF(..),
    render,
    match,
    applyMapLeft,
    applyMapRight,
    reLabel,
    reLabelAll
) where

import Data.Function (on)
import Control.Applicative (liftA2)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import Control.Monad.State (State)
import qualified Control.Monad.State as S

import Mapping (Mapping(..), BiMapping(..))

-- Logical connectives
infix 5 :|:
infix 5 :&:
infix 5 :>:
infix 5 :=:

-- Logical formula datatype
data WFF c =
    Prop c |                -- Proposition
    Not (WFF c) |           -- Negation
    (:|:) (WFF c) (WFF c) | -- Disjunction
    (:&:) (WFF c) (WFF c) | -- Conjunction
    (:>:) (WFF c) (WFF c) | -- Implication
    (:=:) (WFF c) (WFF c)   -- Equivalence
    deriving Eq

-- Get the infix constructors to render properly
instance Show c => Show (WFF c) where
    showsPrec prec (Prop prop) =
        showParen (prec>10) $ showString "Prop " . showsPrec 11 prop
    showsPrec prec (Not wff) =
        showParen (prec>10) $ showString "Not " . showsPrec 11 wff
    showsPrec prec (wff1 :|: wff2) =
        showParen (prec>5) $
            showsPrec 6 wff1 . showString " :|: " . showsPrec 6 wff2
    showsPrec prec (wff1 :&: wff2) =
        showParen (prec>5) $
            showsPrec 6 wff1 . showString " :&: " . showsPrec 6 wff2
    showsPrec prec (wff1 :>: wff2) =
        showParen (prec>5) $
            showsPrec 6 wff1 . showString " :>: " . showsPrec 6 wff2
    showsPrec prec (wff1 :=: wff2) =
        showParen (prec>5) $
            showsPrec 6 wff1 . showString " :=: " . showsPrec 6 wff2

-- Apply functions to propositions
instance Functor WFF where
    fmap f (Prop prop) = Prop $ f prop
    fmap f (Not wff) = Not $ fmap f wff
    fmap f (wff1 :|: wff2) = ((:|:) `on` fmap f) wff1 wff2
    fmap f (wff1 :&: wff2) = ((:&:) `on` fmap f) wff1 wff2
    fmap f (wff1 :>: wff2) = ((:>:) `on` fmap f) wff1 wff2
    fmap f (wff1 :=: wff2) = ((:=:) `on` fmap f) wff1 wff2

{-
    The Monad and Applicative instances basically nest later structures into
    earlier structures. The main point of this is that >>= can be used to
    substitute propositions for formulas
-}
instance Applicative WFF where
    pure = Prop
    (Prop f) <*> wff = f <$> wff
    (Not wff1) <*> wff2 = Not $ wff1 <*> wff2
    (left :|: right) <*> wff = ((:|:) `on` (<*> wff)) left right
    (left :&: right) <*> wff = ((:&:) `on` (<*> wff)) left right
    (left :>: right) <*> wff = ((:>:) `on` (<*> wff)) left right
    (left :=: right) <*> wff = ((:=:) `on` (<*> wff)) left right

instance Monad WFF where
    (Prop prop) >>= f = f prop
    (Not wff) >>= f = Not $ wff >>= f
    (wff1 :|: wff2) >>= f = ((:|:) `on` (>>= f)) wff1 wff2
    (wff1 :&: wff2) >>= f = ((:&:) `on` (>>= f)) wff1 wff2
    (wff1 :>: wff2) >>= f = ((:>:) `on` (>>= f)) wff1 wff2
    (wff1 :=: wff2) >>= f = ((:=:) `on` (>>= f)) wff1 wff2

-- Fold over the propositions in left to right order
instance Foldable WFF where
    foldMap f (Prop prop) = f prop
    foldMap f (Not wff) = foldMap f wff
    foldMap f (wff1 :|: wff2) = (mappend `on` foldMap f) wff1 wff2
    foldMap f (wff1 :&: wff2) = (mappend `on` foldMap f) wff1 wff2
    foldMap f (wff1 :>: wff2) = (mappend `on` foldMap f) wff1 wff2
    foldMap f (wff1 :=: wff2) = (mappend `on` foldMap f) wff1 wff2

-- Traverse the propositions left to right
instance Traversable WFF where
    sequenceA (Prop prop) = Prop <$> prop
    sequenceA (Not wff) = Not <$> sequenceA wff
    sequenceA (wff1 :|: wff2) = (liftA2 (:|:) `on` sequenceA) wff1 wff2
    sequenceA (wff1 :&: wff2) = (liftA2 (:&:) `on` sequenceA) wff1 wff2
    sequenceA (wff1 :>: wff2) = (liftA2 (:>:) `on` sequenceA) wff1 wff2
    sequenceA (wff1 :=: wff2) = (liftA2 (:=:) `on` sequenceA) wff1 wff2

-- Nice rendering for the user
rendersPrec :: Int -> (c -> String) -> WFF c -> ShowS
rendersPrec _ rend (Prop prop) = showString $ rend prop
rendersPrec prec rend (Not wff) = showParen (prec>2) $
    showString "¬" . rendersPrec 2 rend wff
rendersPrec prec rend (wff1 :|: wff2) = showParen (prec>1) $
    rendersPrec 2 rend wff1 . showString "∨" . rendersPrec 2 rend wff2
rendersPrec prec rend (wff1 :&: wff2) = showParen (prec>1) $
    rendersPrec 2 rend wff1 . showString "∧" . rendersPrec 2 rend wff2
rendersPrec prec rend (wff1 :>: wff2) = showParen (prec>1) $
    rendersPrec 2 rend wff1 . showString "→" . rendersPrec 2 rend wff2
rendersPrec prec rend (wff1 :=: wff2) = showParen (prec>1) $
    rendersPrec 2 rend wff1 . showString "↔" . rendersPrec 2 rend wff2

render :: (c -> String) -> WFF c -> String
render rend wff = rendersPrec 2 rend wff ""

{-
    Match two WFFs, returning substitutions to turn each into the other
    after substitutions have been applied
-}
match :: (Ord x, Ord y) => WFF x -> WFF y -> BiMapping WFF x y
match a@(Prop prop1) b@(Prop prop2) = BiMapping $
    Just (M.singleton prop1 b, M.singleton prop2 a)
match (Prop prop) wff = BiMapping $ Just (M.singleton prop wff, M.empty)
match wff (Prop prop) = BiMapping $ Just (M.empty, M.singleton prop wff)
match (Not wff1) (Not wff2) = match wff1 wff2
match (left1 :|: right1) (left2 :|: right2) =
    match left1 left2 <> match right1 right2
match (left1 :&: right1) (left2 :&: right2) =
    match left1 left2 <> match right1 right2
match (left1 :>: right1) (left2 :>: right2) =
    match left1 left2 <> match right1 right2
match (left1 :=: right1) (left2 :=: right2) =
    match left1 left2 <> match right1 right2
match _ _ = BiMapping Nothing

-- Apply the substitutions to the left wff
applyMapLeft :: Ord x => Map x (WFF y) -> WFF x -> WFF (Either x y)
applyMapLeft m wff = do
    prop <- wff
    case M.lookup prop m of
        Just newWff -> Right <$> newWff
        Nothing -> Prop $ Left prop

-- Apply the substitutions to the right wff
applyMapRight :: Ord y => Map y (WFF x) -> WFF y -> WFF (Either x y)
applyMapRight m wff = do
    prop <- wff
    case M.lookup prop m of
        Just newWff -> Left <$> newWff
        Nothing -> Prop $ Right prop

{-
    Given an infinite list of proposition labels,
    replaces the propositions in a wff with the ones in the labels
-}
reLabel :: Ord x => [y] -> WFF x -> WFF y
reLabel labels wff = S.evalState (reLabelState wff) (labels, M.empty)

-- Relabels all formulas in a list
reLabelAll :: (Ord x, Traversable t) => [y] -> t (WFF x) -> t (WFF y)
reLabelAll labels list = S.evalState (traverse reLabelState list) (labels, M.empty)

reLabelState :: Ord x => WFF x -> State ([y], Map x y) (WFF y)
reLabelState = sequenceA . fmap reLabelProp

reLabelProp :: Ord x => x -> State ([y], Map x y) y
reLabelProp prop = S.get >>= \(free, used) ->
    case M.lookup prop used of
        Just label -> return label
        Nothing -> head free <$
            S.put (tail free, M.insert prop (head free) used)
