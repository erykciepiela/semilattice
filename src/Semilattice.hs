module Semilattice where

import Data.Set
import Data.Semigroup
import Data.Map.Append
import Data.List

class Semigroup s => Semilattice s where
    -- a <> b = b <> a - commutativity, saves us from out of order messages problem
    -- a <> a = a - idempotence, saves us from exactly-once delivery guarantee problem

merge :: Semilattice s => s -> s -> s
merge = (<>)

instance (Ord k, Semilattice v) => Semilattice (AppendMap k v)

instance Ord a => Semilattice (Set a)

instance (Ord a, Bounded a) => Semilattice (Max a)

instance Semilattice All

instance Semilattice Any

newtype SList a = SList { slist :: [a] } 

deriving instance Show a => Show (SList a)

instance Semigroup a => Semigroup (SList a) where
    l1 <> l2 = SList $ foldl1 (<>) <$> transpose [slist l1, slist l2]

instance Semilattice a => Semilattice (SList a) where