module Semilattice (
    BoundedJoinSemilattice(..),
    (+>),
    (<+),
    (<<+),
    (+>>),
    (<+>),
    Based(..),
    -- | Primitive join semilattices 
    Increasing(..),
    propagateIncrease,
    Decreasing(..),
    propagateDecrease,
    Same(..),
    propagateSame,
    Growing(..),
    propagateGrowth,
    Shrinking(..),
    propagateShrink,
    -- | Higher-order join semilattices
) where

import Prelude hiding (id, (.))
import Data.Set as S
import Data.Semigroup
import qualified Data.Map as M
import Data.List
import Control.Category
import Data.Proxy
import Data.Functor.Identity
import Data.Void

class JoinSemilattice s where
    -- a \/ (b  \/ c) = (a \/ n) \/ c - associativity
    -- a \/ b = b \/ a - commutativity, saves us from out of order messages problem
    -- a \/ a = a idempotence, saves us from exactly-once delivery guarantee problem
    (\/) :: s -> s -> s

class (Monoid s, JoinSemilattice s) => BoundedJoinSemilattice s where
    bottom :: s

bjsconcat :: (Ord s, BoundedJoinSemilattice s) => S.Set s -> s
bjsconcat = S.foldr (<>) mempty

bjsconcat' :: (Foldable f, BoundedJoinSemilattice s) => f s -> s
bjsconcat' = Prelude.foldr (<>) mempty
-- if f s is bounded join semilattice then it's a propagator

bjsconcat'' :: (Foldable f, BoundedJoinSemilattice s, BoundedJoinSemilattice (f s)) => f s -> s
bjsconcat'' = Prelude.foldr (<>) mempty

(+>) :: (Eq s, BoundedJoinSemilattice s) => s -> s -> Bool
s1 +> s2 = s1 \/ s2 == s1

(+>>) :: (Eq s, BoundedJoinSemilattice s) => s -> s -> Bool
s1 +>> s2 = s1 +> s2 && s1 /= s2

(<+) :: (Eq s, BoundedJoinSemilattice s) => s -> s -> Bool
(<+) = flip (+>)

(<<+) :: (Eq s, BoundedJoinSemilattice s) => s -> s -> Bool
s1 <<+ s2 = s1 <+ s2 && s1 /= s2

-- is comparable
(<+>) :: (Eq s, BoundedJoinSemilattice s) => s -> s -> Bool
s1 <+> s2 = s1 <+ s2 || s1 +> s2

isAscending :: (Eq s, BoundedJoinSemilattice s) => [s] -> Bool
isAscending [] = True
isAscending [s] = True
isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest

isDescending :: (Eq s, BoundedJoinSemilattice s) => [s] -> Bool
isDescending [] = True
isDescending [s] = True
isDescending (s1:rest@(s2:_)) = s1 +> s2 && isDescending rest

--
class BoundedJoinSemilattice s => Based s b | s -> b where
    base :: b -> s

-- 
instance JoinSemilattice () where
    (\/) = (<>)

instance BoundedJoinSemilattice () where
    bottom = mempty

instance Based () () where
    base = id

--
instance (Ord a, Bounded a) => JoinSemilattice (Max a ) where
    (\/) = (<>)

instance (Ord a, Bounded a) => BoundedJoinSemilattice (Max a) where
    bottom = mempty

instance (Ord a, Bounded a) => Based (Max a) a where
    base = Max

--
instance (Ord a, Bounded a) => JoinSemilattice (Min a) where
    (\/) = (<>)

instance (Ord a, Bounded a) => BoundedJoinSemilattice (Min a) where
    bottom = mempty

instance (Ord a, Bounded a) => Based (Min a) a where
    base = Min

--
instance JoinSemilattice All where
    (\/) = (<>)

instance BoundedJoinSemilattice All  where
    bottom = mempty

--
instance JoinSemilattice Any where
    (\/) = (<>)

instance BoundedJoinSemilattice Any  where
    bottom = mempty

--
instance JoinSemilattice (Proxy a) where
    (\/) = (<>)

instance BoundedJoinSemilattice (Proxy a) where
    bottom = mempty

instance Based (Proxy a) () where
    base _ = Proxy


-- | If @a@ is Ord and Bounded and we know it increases in time.
-- | Equivalent to Max.
newtype Increasing a = Increasing { increasing :: a }

instance Ord a => Semigroup (Increasing a) where
    (Increasing a) <> (Increasing b) = Increasing (Prelude.max a b)

instance (Ord a, Bounded a) => Monoid (Increasing a) where
    mempty = Increasing minBound

deriving instance Eq a => Eq (Increasing a)

instance Ord a => JoinSemilattice (Increasing a) where
    (\/) = (<>)
    
instance (Ord a, Bounded a) => BoundedJoinSemilattice (Increasing a) where
    bottom = mempty

instance (Ord a, Bounded a) => Based (Increasing a) a where
    base = Increasing

propagateIncrease :: (a -> b) -> Increasing a -> Increasing b
propagateIncrease f (Increasing a) = Increasing (f a) -- f must be monotone

-- | If @a@ is Ord and Bounded and we know it decreases in time.
-- | Equivalent to Min.
newtype Decreasing a = Decreasing { decreasing :: a }

instance Ord a => Semigroup (Decreasing a) where
    (Decreasing a) <> (Decreasing b) = Decreasing (Prelude.min a b)

instance (Ord a, Bounded a) => Monoid (Decreasing a) where
    mempty = Decreasing maxBound

deriving instance Eq a => Eq (Decreasing a)

instance Ord a => JoinSemilattice (Decreasing a) where
    (\/) = (<>)

instance (Ord a, Bounded a) => BoundedJoinSemilattice (Decreasing a) where
    bottom = mempty

instance (Ord a, Bounded a) => Based (Decreasing a) a where
    base = Decreasing

propagateDecrease :: (a -> b) -> Decreasing a -> Decreasing b
propagateDecrease f (Decreasing a) = Decreasing (f a) -- f must be counter-monotone

-- | If @a@ is Ord and we know we get more of them over time.
newtype Growing a = Growing { growing :: Set a }

deriving instance Eq a => Eq (Growing a)
deriving instance Show a => Show (Growing a)

instance Ord a => Semigroup (Growing a) where
    s1 <> s2 = Growing $ S.union (growing s1) (growing s2)

instance Ord a => Monoid (Growing a) where
    mempty = Growing $ mempty

instance Ord a => JoinSemilattice (Growing a) where
    (\/) = (<>)

instance Ord a => BoundedJoinSemilattice (Growing a) where
    bottom = mempty

instance Ord a => Based (Growing a) a where
    base = Growing . S.singleton

propagateGrowth :: (Ord a, Ord b) => (a -> b) -> Growing a -> Growing b
propagateGrowth f = Growing . S.map f . growing

-- | If @a@ is Ord and we know we get fewer of them over time.
newtype Shrinking a = Shrinking { shrinking :: Set a }

deriving instance Eq a => Eq (Shrinking a)

instance Ord a => Semigroup (Shrinking a) where
    s1 <> s2 = Shrinking $ S.intersection (shrinking s1) (shrinking s2)

instance (Ord a, Enum a, Bounded a) => Monoid (Shrinking a) where
    mempty = Shrinking $ S.fromList $ enumFromTo minBound maxBound

instance Ord a => JoinSemilattice (Shrinking a) where
    (\/) = (<>)

instance (Ord a, Enum a, Bounded a) => BoundedJoinSemilattice (Shrinking a) where
    bottom = mempty

instance (Ord a, Enum a, Bounded a) => Based (Shrinking a) a where
    base a = Shrinking $ S.delete a (S.fromList $ enumFromTo minBound maxBound)

propagateShrink :: (Ord a, Ord b) => (a -> b) -> Shrinking a -> Shrinking b
propagateShrink f = Shrinking . S.map f . shrinking

-- | If @a@ is Ord and we know we it should stay the same over time.
-- newtype Same a = Same { same :: Either [a] a }
data Same a = Unknown | Unambiguous a | Ambiguous (Set a)

deriving instance Eq a => Eq (Same a)
deriving instance Show a => Show (Same a)

instance Ord a => Semigroup (Same a) where
    Unknown <> p = p
    p <> Unknown = p
    Ambiguous as <> Unambiguous a = Ambiguous (S.insert a as) 
    Unambiguous a <> Ambiguous as = Ambiguous (S.insert a as) 
    Ambiguous as1 <> Ambiguous as2 = Ambiguous (S.union as1 as2)
    p@(Unambiguous a1) <> (Unambiguous a2)
        | a1 == a2 = p
        | otherwise = Ambiguous (S.fromList [a1, a2])

instance Ord a => Monoid (Same a) where
    mempty = Unknown

instance Ord a => JoinSemilattice (Same a) where
    (\/) = (<>)

instance Ord a => BoundedJoinSemilattice (Same a) where
    bottom = mempty

instance Ord a => Based (Same a) a where
    base = Unambiguous


propagateSame :: (Ord a, Ord b) => (a -> b) -> Same a -> Same b
propagateSame f Unknown = Unknown
propagateSame f (Unambiguous a) = Unambiguous (f a)
propagateSame f (Ambiguous as) = Ambiguous (S.map f as)

-- higher order join semilattices

--
instance JoinSemilattice a => JoinSemilattice (Identity a) where
    Identity a1 \/ Identity a2 = Identity $ a1 \/ a2

instance BoundedJoinSemilattice a => BoundedJoinSemilattice (Identity a) where
    bottom = mempty

--
instance (Ord k, JoinSemilattice v) => JoinSemilattice (M.Map k v) where
    (\/) = M.unionWith (\/)

instance (Ord k, BoundedJoinSemilattice v) => BoundedJoinSemilattice (M.Map k v) where
    bottom = mempty

instance (Ord k, BoundedJoinSemilattice v) => Based (M.Map k v) (k, v) where
    base (k, v) = M.singleton k v

--
instance JoinSemilattice a => JoinSemilattice [a] where
    l1 \/ l2 = foldl1 (\/) <$> transpose [l1, l2]

instance BoundedJoinSemilattice a => BoundedJoinSemilattice [a] where
    bottom = mempty

-- 
instance (JoinSemilattice a, JoinSemilattice b) => JoinSemilattice (a, b) where
    (a1, b1) \/ (a2, b2) = (a1 \/ a2, b1 \/ b2)

instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c) => JoinSemilattice (a, b, c) where
    (a1, b1, c1) \/ (a2, b2, c2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2)

instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c, JoinSemilattice d) => JoinSemilattice (a, b, c, d) where
    (a1, b1, c1, d1) \/ (a2, b2, c2, d2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2, d1 \/ d2)

instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b) => BoundedJoinSemilattice (a, b) where
    bottom = mempty

instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b, BoundedJoinSemilattice c) => BoundedJoinSemilattice (a, b, c) where
    bottom = mempty

instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b, BoundedJoinSemilattice c, BoundedJoinSemilattice d) => BoundedJoinSemilattice (a, b, c, d) where
    bottom = mempty

--- and so on...
