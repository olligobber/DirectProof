{-# LANGUAGE RankNTypes #-}

module UnionFind (
    Getter,
    Setter,
    UnionFind,
    UnionFindS,
    new,
    find,
    rep,
    value,
    set,
    union,
    flatten
) where

import Control.Monad.State (State)
import qualified Control.Monad.State as S

-- Gets a value from a map-like type
type Getter m i = forall v. m v -> i -> v

-- Sets a value in a map-like type
type Setter m i = forall v. m v -> i -> v -> m v

-- UnionFind based on an arbitrary map-like type
data UnionFind m i v = UnionFind {
    getter :: Getter m i,
    setter :: Setter m i,
    members :: m (UnionElement i v),
    identity :: m i
}

data UnionElement i v = ChildOf i | Root Integer v

-- Specialised setters and getters for UnionFind
infix 9 !
infix 9 //

(!) :: UnionFind m i v -> i -> UnionElement i v
uf ! index = getter uf (members uf) index

(//) :: UnionFind m i v -> (i, UnionElement i v) -> UnionFind m i v
uf // (index, value) = UnionFind
    (getter uf)
    (setter uf)
    (setter uf (members uf) index value)
    (identity uf)

getRank :: UnionElement i v -> Integer
getRank (Root x _) = x
getRank _ = error "Element is not a root"

getValue :: UnionElement i v -> v
getValue (Root _ x) = x
getValue _ = error "Element is not a root"

{-
    Make a unionfind where everything is seperate given the map-like type
    prefilled with indices mapping to themselves and a value
-}
new :: Functor m => Getter m i -> Setter m i -> m (i, v) -> UnionFind m i v
new get set structure = UnionFind get set
    (Root 0 . snd <$> structure)
    (fst <$> structure)

-- Stateful UnionFind operations
type UnionFindS m i v = State (UnionFind m i v)

-- Stateful getter for unionfind
extract :: i -> UnionFindS m i v (UnionElement i v)
extract mem = S.gets (! mem)
--
-- Set a unionfind element's parent
setparent :: Eq i => i -> i -> UnionFindS m i v ()
setparent child parent
    | child == parent   = error "Tried to make loop in UnionFind"
    | otherwise         = S.modify (// (child, ChildOf parent))

-- Set a unionfind element as a root with a given rank
setrank :: i -> Integer -> UnionFindS m i v ()
setrank root rank = do
    rootVal <- extract root
    case rootVal of
        ChildOf _ -> error "Tried to make non-root of UnionFind into a root"
        Root _ value -> S.modify (// (root, Root rank value))

-- Set a unionfind element as a root with a given value
setvalue :: i -> v -> UnionFindS m i v ()
setvalue root value = do
    rootVal <- extract root
    case rootVal of
        ChildOf _ -> error "Tried to set value of non-root of UnionFind"
        Root rank _ -> S.modify (// (root, Root rank value))

-- Find the representative and value of an element's set
find :: Eq i => i -> UnionFindS m i v (i,v)
find mem = do
    memele <- extract mem
    case memele of
        Root _ value -> return (mem, value)
        ChildOf par -> do
            (root,value) <- find par
            setparent mem root
            return (root,value)

-- Find the representative of an element's set
rep :: Eq i => i -> UnionFindS m i v i
rep mem = fst <$> find mem

-- Find the value of an element's set
value :: Eq i => i -> UnionFindS m i v v
value mem = snd <$> find mem

-- Set the value of an element's set
set :: Eq i => i -> v -> UnionFindS m i v ()
set index value = do
    root <- rep index
    setvalue root value

-- Join two sets, returning the two values if a merge occurred
union :: Eq i => i -> i -> UnionFindS m i v (Maybe (v,v))
union mem1 mem2 = do
    (root1, value1) <- find mem1
    (root2, value2) <- find mem2
    if root1 == root2 then return Nothing else do
        rank1 <- getRank <$> extract root1
        rank2 <- getRank <$> extract root2
        case compare rank1 rank2 of
            GT -> setparent root2 root1
            LT -> setparent root1 root2
            EQ -> do
                setparent root1 root2
                setrank root2 $ rank2 + 1
        return $ Just (value1, value2)

{-
    Extract the underlying map-like type mapping each element to its
    representative and value
-}
flatten :: (Eq i, Traversable m) => UnionFindS m i v (m (i,v))
flatten = S.gets identity >>= mapM find
