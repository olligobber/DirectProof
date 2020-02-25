{-# LANGUAGE FlexibleInstances #-}

module Logical (
    Logical(..),
    evaluate,
    counterexample
) where

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import Data.Function (on)

import WFF(WFF(..))

class Eq x => Logical x where
    meet :: x -> x -> x -- Logical and
    join :: x -> x -> x -- Logical or
    neg :: x -> x -- Logical not
    top :: x -- Logical true
    bot :: x -- Logical false

instance Logical Bool where
    meet = (&&)
    join = (||)
    neg = not
    top = True
    bot = False

instance Logical (Maybe Bool) where
    meet (Just True) (Just True) = Just True
    meet (Just False) _ = Just False
    meet _ (Just False) = Just False
    meet _ _ = Nothing

    join (Just False) (Just False) = Just False
    join (Just True) _ = Just True
    join _ (Just True) = Just True
    join _ _ = Nothing

    neg = fmap not
    top = Just True
    bot = Just False

evaluate :: Logical x => WFF x -> x
evaluate (Prop x) = x
evaluate (Not w) = neg $ evaluate w
evaluate (left :|: right) = (join `on` evaluate) left right
evaluate (left :&: right) = (meet `on` evaluate) left right
evaluate (left :>: right) = evaluate $ Not left :|: right
evaluate (left :=: right) = evaluate $ (left :>: right) :&: (right :>: left)

counterexample :: (Ord x, Logical y) => [y] -> WFF x -> WFF x -> Maybe (Map x y)
counterexample vals first second =
    case filter (not . sateval second) $ filter (sateval first) tables of
        [] -> Nothing
        (x:_) -> Just x
    where
        props = S.toList $
            foldMap S.singleton first <> foldMap S.singleton second
        tables = M.fromList <$> mapM (\x -> [(,) x] <*> vals) props
        sateval wff table = evaluate ((table M.!) <$> wff) == top
