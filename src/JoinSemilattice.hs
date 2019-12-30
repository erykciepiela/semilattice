module JoinSemilattice where

import Prelude hiding (id, (.))
import Data.Set as S
import Data.Semigroup
import Data.Map.Append
import Data.List
import Control.Arrow
import Control.Concurrent.STM
import Control.Category

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

instance (JoinSemilattice a, JoinSemilattice b) => JoinSemilattice (a, b) where

isMonotone :: (JoinSemilattice a, JoinSemilattice b) => (a -> b) -> a -> a -> Bool
isMonotone f a1 a2 = f (a1 <> a2) +> f a1 && f (a1 <> a2) +> f a2

data Monotone a b where
    -- f (a1 <> a2) +> f a1
    -- f (a1 <> a2) +> f a2
    Monotone :: (JoinSemilattice a, JoinSemilattice b) => (a -> b) -> Monotone a b
    IdMonotone :: Monotone a a

instance Category Monotone where
    id = IdMonotone
    m . IdMonotone = m
    IdMonotone . m = m
    (Monotone p2) . (Monotone p1) = Monotone (p2 . p1)

propagate :: Monotone a b -> a -> b
propagate IdMonotone = id
propagate (Monotone f) = f

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

instance (Ord k, JoinSemilattice v) => JoinSemilattice (AppendMap k v)

instance Ord a => JoinSemilattice (Set a)

instance (Ord a, Bounded a) => JoinSemilattice (Max a)

instance JoinSemilattice All

instance JoinSemilattice Any


newtype SList a = SList { slist :: [a] } 

deriving instance Show a => Show (SList a)

instance Semigroup a => Semigroup (SList a) where
    l1 <> l2 = SList $ foldl1 (<>) <$> transpose [slist l1, slist l2]

instance JoinSemilattice a => JoinSemilattice (SList a) where

instance (Eq a) => Eq (SList a) where
