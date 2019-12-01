module Semilattice where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Semigroup

-- | <> denotes "merging" knowledge
-- | commutativity saves us from out of order messages problem
-- | idempotence saves us from exactly-once delivery guarantee problem
class (Eq s, Monoid s) => Semilattice s where
    -- a <> b = b <> a - commutativity
    -- a <> a = a - idempotence

isAchieved :: Semilattice s => s -> s -> Bool
isAchieved goal s = s <> goal == s

leads :: Semilattice s => s -> s -> s -> Bool
leads source step target = source <> step <> target == target

isAchieved' :: Semilattice s => s -> [s] -> Bool
isAchieved' goal ss = isAchieved goal (mconcat ss)

areAchieved' :: Semilattice s => [s] -> [s] -> Bool
areAchieved' goals ss = isAchieved (mconcat goals) (mconcat ss)

-- | Wrapper over map that instantiates semilattice
newtype SMap k v = SMap { smap :: M.Map k v}

deriving instance (Show k, Show v) => Show (SMap k v)
deriving instance (Eq k, Eq v) => Eq (SMap k v)

instance (Ord k, Semigroup v) => Semigroup (SMap k v) where
    mm1 <> mm2 = SMap $ M.unionWith (<>) (smap mm1) (smap mm2)

instance (Ord k, Semigroup v) => Monoid (SMap k v) where
    mempty = SMap M.empty 

instance (Ord k, Eq k, Semilattice v) => Semilattice (SMap k v)

-- | Wrapper over set that instantiates samilattice
data SSet a = SSet { sset :: S.Set a}

deriving instance Show a => Show (SSet a)
deriving instance Eq a => Eq (SSet a)

instance Ord a => Semigroup (SSet a) where
    s1 <> s2 = SSet (sset s1 `S.union` sset s2)

instance Ord a => Monoid (SSet a) where
    mempty = SSet S.empty 

instance Ord a => Semilattice (SSet a)

-- |
instance (Eq a, Ord a, Bounded a) => Semilattice (Max a)
