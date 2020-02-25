{-# LANGUAGE OverloadedStrings #-}

module WFF(
    WFF(..),
    MatchError(..),
    matchPref,
    match,
    applyMap
) where

import Data.Function (on)
import Control.Applicative (liftA2)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import Control.Monad (ap)
import Control.Monad.Identity (runIdentity)
import Data.Traversable (foldMapDefault)
import Data.Text (Text)
import Control.Monad.State (State, StateT)
import qualified Control.Monad.State as S
import Data.Maybe (fromMaybe)

import UnionFind (UnionFind)
import qualified UnionFind as U
import Render (RenderableF(..))

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

instance Functor WFF where -- Use Monad instance to define this
    fmap f m = m >>= (return . f)

instance Applicative WFF where -- Use Monad instance to define this
    pure = return
    (<*>) = ap

{-
    The Monad and Applicative instances basically nest later structures into
    earlier structures. The main point of this is that >>= can be used to
    substitute propositions for formulas
-}
instance Monad WFF where
    return = Prop
    (Prop prop)     >>= f   = f prop
    (Not wff)       >>= f   = Not $ wff >>= f
    (wff1 :|: wff2) >>= f   = ((:|:) `on` (>>= f)) wff1 wff2
    (wff1 :&: wff2) >>= f   = ((:&:) `on` (>>= f)) wff1 wff2
    (wff1 :>: wff2) >>= f   = ((:>:) `on` (>>= f)) wff1 wff2
    (wff1 :=: wff2) >>= f   = ((:=:) `on` (>>= f)) wff1 wff2

instance Foldable WFF where -- Use Traversable instance to define this
    foldMap = foldMapDefault

instance Traversable WFF where
    sequenceA (Prop prop) = Prop <$> prop
    sequenceA (Not wff) = Not <$> sequenceA wff
    sequenceA (wff1 :|: wff2) = (liftA2 (:|:) `on` sequenceA) wff1 wff2
    sequenceA (wff1 :&: wff2) = (liftA2 (:&:) `on` sequenceA) wff1 wff2
    sequenceA (wff1 :>: wff2) = (liftA2 (:>:) `on` sequenceA) wff1 wff2
    sequenceA (wff1 :=: wff2) = (liftA2 (:=:) `on` sequenceA) wff1 wff2

showParenT :: Bool -> (Text -> Text) -> Text -> Text
showParenT False t = t
showParenT True t = ("(" <>) . t . (")" <>)

showText :: Text -> (Text -> Text)
showText = (<>)

-- Nice rendering for the user
rendersPrec :: Int -> (c -> Text) -> WFF c -> Text -> Text
rendersPrec _ rend (Prop prop) = showText $ rend prop
rendersPrec prec rend (Not wff) = showParenT (prec>2) $
    showText "¬" . rendersPrec 2 rend wff
rendersPrec prec rend (wff1 :|: wff2) = showParenT (prec>1) $
    rendersPrec 2 rend wff1 . showText "∨" . rendersPrec 2 rend wff2
rendersPrec prec rend (wff1 :&: wff2) = showParenT (prec>1) $
    rendersPrec 2 rend wff1 . showText "∧" . rendersPrec 2 rend wff2
rendersPrec prec rend (wff1 :>: wff2) = showParenT (prec>1) $
    rendersPrec 2 rend wff1 . showText "→" . rendersPrec 2 rend wff2
rendersPrec prec rend (wff1 :=: wff2) = showParenT (prec>1) $
    rendersPrec 2 rend wff1 . showText "↔" . rendersPrec 2 rend wff2

instance RenderableF WFF where
    renders rend wff = rendersPrec 2 rend wff ""

-- Possible errors that can occur when trying to match WFFs
data MatchError x =
    -- Two sub-WFFs can have differing structures
    StructureError (WFF x) (WFF x) |
    -- A proposition can be matched to a WFF containing itself
    RecursionError x (WFF x)
    deriving Show

-- Convert stateful computations from UnionFind to use the Either monad
toUWFF :: State (UnionFind (Map x) x (Maybe (WFF x))) v ->
    StateT (UnionFind (Map x) x (Maybe (WFF x))) (Either (MatchError x)) v
toUWFF = S.mapStateT (return . runIdentity)

-- Statefully match two WFFs, with a function to determine prefered propositions
matchS :: Ord x => (x -> Bool) -> WFF x -> WFF x ->
    StateT (UnionFind (Map x) x (Maybe (WFF x))) (Either (MatchError x)) ()
matchS f (Prop prop1) (Prop prop2) = do
    merged <- toUWFF $ U.union prop1 prop2
    newrep <- toUWFF $ U.rep prop1
    case merged of
        Nothing -> return ()
        Just (Nothing, Nothing) | f prop1 && newrep == prop2 ->
            toUWFF $ U.set prop1 (Just $ Prop prop1)
        Just (Nothing, Nothing) | f prop2 && newrep == prop1 ->
            toUWFF $ U.set prop1 (Just $ Prop prop2)
        Just (Nothing, x) -> toUWFF $ U.set prop1 x
        Just (x, Nothing) -> toUWFF $ U.set prop1 x
        Just (Just (Prop _), x) -> toUWFF $ U.set prop1 x
        Just (x, Just (Prop _)) -> toUWFF $ U.set prop1 x
        Just (Just x, Just y) -> matchS f x y
matchS f (Prop prop1) y = do
    val <- toUWFF $ U.value prop1
    case val of
        Nothing -> toUWFF $ U.set prop1 $ Just y
        Just (Prop _) -> toUWFF $ U.set prop1 $ Just y
        Just x -> matchS f x y
matchS f x (Prop prop1) = matchS f (Prop prop1) x
matchS f (Not wff1) (Not wff2) = matchS f wff1 wff2
matchS f (left1 :|: right1) (left2 :|: right2) =
    matchS f left1 left2 >> matchS f right1 right2
matchS f (left1 :&: right1) (left2 :&: right2) =
    matchS f left1 left2 >> matchS f right1 right2
matchS f (left1 :>: right1) (left2 :>: right2) =
    matchS f left1 left2 >> matchS f right1 right2
matchS f (left1 :=: right1) (left2 :=: right2) =
    matchS f left1 left2 >> matchS f right1 right2
matchS _ x y = S.StateT $ const $ Left $ StructureError x y

-- The first part of matching two WFFs, which collects all matched propositions
matchPart :: Ord x => (x -> Bool) -> WFF x -> WFF x ->
    Either (MatchError x) (Map x (WFF x))
matchPart f x y = fmap (\(k, v) -> fromMaybe (Prop k) v) <$> S.evalStateT
    (matchS f x y >> toUWFF U.flatten)
    (U.new
        (M.!)
        (\m k v -> M.insert k v m)
        (((<>) `on` foldMap (\k -> M.singleton k (k, Nothing))) x y)
    )

-- Statefully remove all occurrences of a proposition that doesn't map to itself
flattenS :: Ord x => x -> StateT (Map x (WFF x)) (Either (MatchError x)) ()
flattenS p = do
    m <- S.get
    case M.lookup p m of
        Nothing -> return ()
        Just (Prop q) | p == q -> return ()
        Just w | p `elem` w -> S.StateT $ const $ Left $ RecursionError p w
        Just w -> S.modify (fmap (>>= \q -> if p == q then w else Prop q))

-- Remove all occurrences of propositions that don't map to themselves
flatten :: Ord x => Map x (WFF x) -> Either (MatchError x) (Map x (WFF x))
flatten m = S.execStateT (traverse flattenS (M.keys m)) m

-- Match two WFFs, using the function to prefer certain propositions
matchPref :: Ord x => (x -> Bool) -> WFF x -> WFF x ->
    Either (MatchError x) (Map x (WFF x))
matchPref f x y = matchPart f x y >>= flatten

-- Match two WFFs, returning a mapping to turn both into a common form
match :: Ord x => WFF x -> WFF x -> Either (MatchError x) (Map x (WFF x))
match = matchPref (const False)

-- Apply a mapping from match to some formula
applyMap :: Ord x => Map x (WFF x) -> WFF x -> WFF x
applyMap m w = w >>= \p -> case M.lookup p m of
    Nothing -> Prop p
    Just n -> n
