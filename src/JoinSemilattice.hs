module JoinSemilattice (
    JoinSemilattice,
    (+>),
    (<+),
    (<<+),
    (+>>),
    (<+>),
    UnionSet,
    IntersectionSet,
    List,
    Map,
    JoinSemilattice.map,
    JoinSemilattice.max,
    Promise,
    Data.Semigroup.Max,
    Monotone(..),
    propagate,
    SemiLat(..),
    Entity,
) where

import Prelude hiding (id, (.))
import Data.Set as S
import Data.Semigroup
import qualified Data.Map as M
import Data.Map.Append
import Data.List
import Control.Category
import Data.Proxy
import Data.Functor.Identity
import Data.Void
import Data.IntMap.Strict

class (Eq s, Semigroup s) => JoinSemilattice s where
    -- a <> b = b <> a - commutativity, saves us from out of order messages problem
    -- a <> a = a - idempotence, saves us from exactly-once delivery guarantee problem

(+>) :: JoinSemilattice s => s -> s -> Bool
s1 +> s2 = s1 <> s2 == s1

(+>>) :: JoinSemilattice s => s -> s -> Bool
s1 +>> s2 = s1 +> s2 && s1 /= s2

(<+) :: JoinSemilattice s => s -> s -> Bool
(<+) = flip (+>)

(<<+) :: JoinSemilattice s => s -> s -> Bool
s1 <<+ s2 = s1 <+ s2 && s1 /= s2

-- is comparable
(<+>) :: JoinSemilattice s => s -> s -> Bool
s1 <+> s2 = s1 <+ s2 || s1 +> s2

isAscending :: JoinSemilattice s => [s] -> Bool
isAscending [] = True
isAscending [s] = True
isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest

isDescending :: JoinSemilattice s => [s] -> Bool
isDescending [] = True
isDescending [s] = True
isDescending (s1:rest@(s2:_)) = s1 +> s2 && isDescending rest

-- empty (no values) join semilattice
instance JoinSemilattice Void

-- elementary (single value) join semilattice
instance JoinSemilattice ()

-- (no value - a value - contradiction) join semilattice
data Promise a = None | Promised a | Contradicted 

deriving instance (Eq a) => Eq (Promise a)

instance Functor Promise where
    fmap _ None = None
    fmap _ Contradicted = Contradicted
    fmap f (Promised a) = Promised (f a)

instance Applicative Promise where
    pure = Promised
    None <*> _ = None
    _ <*> None = None
    Contradicted <*> _ = Contradicted
    _ <*> Contradicted = Contradicted
    (Promised f) <*> (Promised a) = Promised (f a)

instance Eq a => Semigroup (Promise a) where
    None <> p = p
    p <> None = p
    Contradicted <> _ = Contradicted
    _ <> Contradicted = Contradicted
    p@(Promised a1) <> (Promised a2)
        | a1 == a2 = p
        | otherwise = Contradicted

instance Eq a => JoinSemilattice (Promise a)

-- product join semilattice
instance (JoinSemilattice a, JoinSemilattice b) => JoinSemilattice (a, b)
instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c) => JoinSemilattice (a, b, c)

-- union set join semilattice
newtype UnionSet a = UnionSet { unionSet :: Set a }

deriving instance Eq a => Eq (UnionSet a)

instance Ord a => Semigroup (UnionSet a) where
    s1 <> s2 = UnionSet $ S.union (unionSet s1) (unionSet s2)

instance Ord a => JoinSemilattice (UnionSet a)

-- intersection set join semilattice
newtype IntersectionSet a = IntersectionSet { intersectionSet :: Set a }

deriving instance Eq a => Eq (IntersectionSet a)

instance Ord a => Semigroup (IntersectionSet a) where
    s1 <> s2 = IntersectionSet $ S.intersection (intersectionSet s1) (intersectionSet s2)

instance Ord a => JoinSemilattice (IntersectionSet a)

-- list join semilattice
newtype List a = List { list :: [a] } 

deriving instance Show a => Show (List a)
deriving instance Eq a => Eq (List a)

instance Semigroup a => Semigroup (List a) where
    l1 <> l2 = List $ foldl1 (<>) <$> transpose [list l1, list l2]

instance JoinSemilattice a => JoinSemilattice (List a) where

-- 
type Map k v = AppendMap k v

instance (Ord k, JoinSemilattice v) => JoinSemilattice (Map k v)

map :: k -> v -> Map k v
map k v = AppendMap (M.singleton k v)

-- emptyMap :: Map k v
-- emptyMap = 

--
instance (Ord a, Bounded a) => JoinSemilattice (Max a)

max :: a -> Max a
max = Max

--
instance (Ord a, Bounded a) => JoinSemilattice (Min a)

instance JoinSemilattice All

instance JoinSemilattice Any

--
instance JoinSemilattice (Proxy a)

instance JoinSemilattice a => JoinSemilattice (Identity a)

data Monotone a b where
    -- f (a1 <> a2) +> f a1
    -- f (a1 <> a2) +> f a2
    Monotone :: (JoinSemilattice a, JoinSemilattice b) => (a -> b) -> Monotone a b
    IdMonotone :: Monotone a a

propagate :: Monotone a b -> a -> b
propagate IdMonotone = id
propagate (Monotone f) = f

foo :: JoinSemilattice a => Monotone a b -> a -> a -> (a, b)
foo m prev a = let new = prev <> a in (new, propagate m new)

data Foo = Foo (Promise Int) (Promise String)

instance Category Monotone where
    id = IdMonotone
    m . IdMonotone = m
    IdMonotone . m = m
    (Monotone p2) . (Monotone p1) = Monotone (p2 . p1)

-- every SemiLat is Monotone
data SemiLat a b where
    -- f (x <> y) = f x <> f y +> f x
    --                         +> f y
    -- f(⊥)=⊥
    Homo :: (JoinSemilattice a, JoinSemilattice b) => (a -> b) -> SemiLat a b
    IdHomo :: SemiLat a a

instance Category SemiLat where
    id = IdHomo
    m . IdHomo = m
    IdHomo . m = m
    (Homo p2) . (Homo p1) = Homo (p2 . p1)
    

--
class JoinSemilattice s => Entity i s o | s -> i o where
    from :: i -> s
    to :: s -> o

-- f s +> s
-- f s <> s = f s
-- s2 +> s1 => f s2 +> f s1
-- f s = s' <> s
-- s2 +> s1 => s' <> s2 +> s' <> s1

-- s2 +> s1 
-- s2 <> s1 = s2
-- s2 <> s1 <> s' = s2 <> s'
-- s2 <> s1 <> s' <> s' = s2 <> s'
-- s2 <> s' <> s1 <> s' = s2 <> s'
-- f s2 <> f s1 = f s2 -- where f s = s' <> s
-- f s2 +> f s1
-- => if f s = s' <> s for given s' then f is monotinic
-- let's call s' an event

