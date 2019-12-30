module JoinSemilattice where

import Data.Set as S
import Data.Semigroup
import Data.Map.Append
import Data.List
import Control.Arrow
import Control.Concurrent.STM

class Semigroup s => JoinSemilattice s where
    -- a <> b = b <> a - commutativity, saves us from out of order messages problem
    -- a <> a = a - idempotence, saves us from exactly-once delivery guarantee problem

(+>) :: (JoinSemilattice s, Eq s) => s -> s -> Bool
s1 +> s2 = s1 <> s2 == s1

(<+) :: (JoinSemilattice s, Eq s) => s -> s -> Bool
(<+) = flip (+>)

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




-- Monototic function over semilattice s
class JoinSemilattice s => Mono m s where
    grow :: m -> s -> s
    -- grow m s <> s = grow m s

instance Mono m s => Mono [m] s where
    grow [] s = s
    grow (m:ms) s = grow ms (grow m s)

-- instance (Mono m s) => Semigroup m where


data SetOp = DoNothing | Add Int

instance Mono SetOp (Set Int) where
    grow DoNothing = id
    grow (Add i) = S.union (singleton i)

-- instance Mono m s => Semigroup m where

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

