module WFF(
    WFF(..),
    render,
    match,
    allMatch
) where

import Data.Function (on)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import Mapping (Mapping(..))

-- Logical formula datatype
infix 5 :|:
infix 5 :&:
infix 5 :>:
infix 5 :=:

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
    showsPrec prec (Prop prop) = showParen (prec>10) $ showString "Prop " . showsPrec 11 prop
    showsPrec prec (Not wff) = showParen (prec>10) $ showString "Not " . showsPrec 11 wff
    showsPrec prec (wff1 :|: wff2) = showParen (prec>5) $ showsPrec 6 wff1 . showString " :|: " . showsPrec 6 wff2
    showsPrec prec (wff1 :&: wff2) = showParen (prec>5) $ showsPrec 6 wff1 . showString " :&: " . showsPrec 6 wff2
    showsPrec prec (wff1 :>: wff2) = showParen (prec>5) $ showsPrec 6 wff1 . showString " :>: " . showsPrec 6 wff2
    showsPrec prec (wff1 :=: wff2) = showParen (prec>5) $ showsPrec 6 wff1 . showString " :=: " . showsPrec 6 wff2

-- Apply functions to propositions
instance Functor WFF where
    fmap f (Prop prop) = Prop $ f prop
    fmap f (Not wff) = Not $ fmap f wff
    fmap f (wff1 :|: wff2) = ((:|:) `on` fmap f) wff1 wff2
    fmap f (wff1 :&: wff2) = ((:&:) `on` fmap f) wff1 wff2
    fmap f (wff1 :>: wff2) = ((:>:) `on` fmap f) wff1 wff2
    fmap f (wff1 :=: wff2) = ((:=:) `on` fmap f) wff1 wff2

-- The Monad and Applicative instances basically nest later structures into earlier structures
-- The main point of this is that >>= can be used to substitute propositions for formulas
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

instance Foldable WFF where
    foldMap f (Prop prop) = f prop
    foldMap f (Not wff) = foldMap f wff
    foldMap f (wff1 :|: wff2) = foldMap f wff1 `mappend` foldMap f wff2
    foldMap f (wff1 :&: wff2) = foldMap f wff1 `mappend` foldMap f wff2
    foldMap f (wff1 :>: wff2) = foldMap f wff1 `mappend` foldMap f wff2
    foldMap f (wff1 :=: wff2) = foldMap f wff1 `mappend` foldMap f wff2

-- Nice rendering for the user
rendersPrec :: Int -> (c -> String) -> WFF c -> ShowS
rendersPrec _ rend (Prop prop) = showString $ rend prop
rendersPrec prec rend (Not wff) = showParen (prec>2) $ showString "¬" . rendersPrec 2 rend wff
rendersPrec prec rend (wff1 :|: wff2) = showParen (prec>1) $ rendersPrec 2 rend wff1 . showString "∨" . rendersPrec 2 rend wff2
rendersPrec prec rend (wff1 :&: wff2) = showParen (prec>1) $ rendersPrec 2 rend wff1 . showString "∧" . rendersPrec 2 rend wff2
rendersPrec prec rend (wff1 :>: wff2) = showParen (prec>1) $ rendersPrec 2 rend wff1 . showString "→" . rendersPrec 2 rend wff2
rendersPrec prec rend (wff1 :=: wff2) = showParen (prec>1) $ rendersPrec 2 rend wff1 . showString "↔" . rendersPrec 2 rend wff2

render :: (c -> String) -> WFF c -> String
render rend wff = rendersPrec 2 rend wff ""

-- -- Match one WFF to another after substitutions have been applied, and return a mapping if it matches
-- match :: (Ord x, Eq y) => WFF x -> WFF y -> Mapping x (WFF y)
-- match (Prop prop) wff = Mapping $ Just $ M.singleton prop wff
-- match (Not wff1) (Not wff2) = match wff1 wff2
-- match (left1 :|: right1) (left2 :|: right2) = match left1 left2 <> match right1 right2
-- match (left1 :&: right1) (left2 :&: right2) = match left1 left2 <> match right1 right2
-- match (left1 :>: right1) (left2 :>: right2) = match left1 left2 <> match right1 right2
-- match (left1 :=: right1) (left2 :=: right2) = match left1 left2 <> match right1 right2
-- match _ _ = Mapping Nothing
--
-- -- Find all sub-formulas that match a given WFF, returning the mapping and placing Prop Nothing in place of the matched formula
-- allMatch :: (Ord x, Eq y) => WFF x -> WFF y -> [(Map x (WFF y), WFF (Maybe y))]
-- allMatch wff1 wff2 = case getMap $ match wff1 wff2 of
--     Just mapping -> (mapping, Prop Nothing) : allMatchSub
--     Nothing -> allMatchSub
--     where
--         allMatchSub = case wff2 of
--             (Prop _) -> []
--             (Not wff) -> fmap Not <$> allMatch wff1 wff
--             (left :|: right) -> (fmap (:|: fmap Just right) <$> allMatch wff1 left) ++ (fmap (fmap Just left :|:) <$> allMatch wff1 right)
--             (left :&: right) -> (fmap (:&: fmap Just right) <$> allMatch wff1 left) ++ (fmap (fmap Just left :&:) <$> allMatch wff1 right)
--             (left :>: right) -> (fmap (:>: fmap Just right) <$> allMatch wff1 left) ++ (fmap (fmap Just left :>:) <$> allMatch wff1 right)
--             (left :=: right) -> (fmap (:=: fmap Just right) <$> allMatch wff1 left) ++ (fmap (fmap Just left :=:) <$> allMatch wff1 right)
