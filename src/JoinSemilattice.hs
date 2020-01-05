module JoinSemilattice (
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
    List,
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

class (Eq s, Semigroup s) => JoinSemilattice s where
    -- a <> b = b <> a - commutativity, saves us from out of order messages problem
    -- a <> a = a - idempotence, saves us from exactly-once delivery guarantee problem

class (Monoid s, JoinSemilattice s) => BoundedJoinSemilattice s where

bjsconcat :: (Ord s, BoundedJoinSemilattice s) => S.Set s -> s
bjsconcat = S.foldr (<>) mempty

bjsconcat' :: (Foldable f, BoundedJoinSemilattice s) => f s -> s
bjsconcat' = Prelude.foldr (<>) mempty
-- if f s is bounded join semilattice then it's a propagator

bjsconcat'' :: (Foldable f, BoundedJoinSemilattice s, BoundedJoinSemilattice (f s)) => f s -> s
bjsconcat'' = Prelude.foldr (<>) mempty

(+>) :: BoundedJoinSemilattice s => s -> s -> Bool
s1 +> s2 = s1 <> s2 == s1

(+>>) :: BoundedJoinSemilattice s => s -> s -> Bool
s1 +>> s2 = s1 +> s2 && s1 /= s2

(<+) :: BoundedJoinSemilattice s => s -> s -> Bool
(<+) = flip (+>)

(<<+) :: BoundedJoinSemilattice s => s -> s -> Bool
s1 <<+ s2 = s1 <+ s2 && s1 /= s2

-- is comparable
(<+>) :: BoundedJoinSemilattice s => s -> s -> Bool
s1 <+> s2 = s1 <+ s2 || s1 +> s2

isAscending :: BoundedJoinSemilattice s => [s] -> Bool
isAscending [] = True
isAscending [s] = True
isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest

isDescending :: BoundedJoinSemilattice s => [s] -> Bool
isDescending [] = True
isDescending [s] = True
isDescending (s1:rest@(s2:_)) = s1 +> s2 && isDescending rest

--
class BoundedJoinSemilattice s => Based s b | s -> b where
    base :: b -> s

-- 
instance JoinSemilattice ()
instance BoundedJoinSemilattice ()

instance Based () () where
    base = id

--
instance (Ord a, Bounded a) => JoinSemilattice (Max a)
instance (Ord a, Bounded a) => BoundedJoinSemilattice (Max a)

instance (Ord a, Bounded a) => Based (Max a) a where
    base = Max

--
instance (Ord a, Bounded a) => JoinSemilattice (Min a)
instance (Ord a, Bounded a) => BoundedJoinSemilattice (Min a)

instance (Ord a, Bounded a) => Based (Min a) a where
    base = Min

--
instance JoinSemilattice All
instance BoundedJoinSemilattice All

--
instance JoinSemilattice Any
instance BoundedJoinSemilattice Any

--
instance JoinSemilattice (Proxy a)
instance BoundedJoinSemilattice (Proxy a)

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

instance Ord a => JoinSemilattice (Increasing a)
instance (Ord a, Bounded a) => BoundedJoinSemilattice (Increasing a)

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

instance Ord a => JoinSemilattice (Decreasing a)
instance (Ord a, Bounded a) => BoundedJoinSemilattice (Decreasing a)

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

instance Ord a => JoinSemilattice (Growing a)
instance Ord a => BoundedJoinSemilattice (Growing a)

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

instance Ord a => JoinSemilattice (Shrinking a)
instance (Ord a, Enum a, Bounded a) => BoundedJoinSemilattice (Shrinking a)

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

instance Ord a => JoinSemilattice (Same a)
instance Ord a => BoundedJoinSemilattice (Same a)

instance Ord a => Based (Same a) a where
    base = Unambiguous


propagateSame :: (Ord a, Ord b) => (a -> b) -> Same a -> Same b
propagateSame f Unknown = Unknown
propagateSame f (Unambiguous a) = Unambiguous (f a)
propagateSame f (Ambiguous as) = Ambiguous (S.map f as)

-- higher order join semilattices

--
instance JoinSemilattice a => JoinSemilattice (Identity a)
instance BoundedJoinSemilattice a => BoundedJoinSemilattice (Identity a)

--
instance (Ord k, JoinSemilattice v) => JoinSemilattice (AppendMap k v)
instance (Ord k, BoundedJoinSemilattice v) => BoundedJoinSemilattice (AppendMap k v)

instance (Ord k, BoundedJoinSemilattice v) => Based (AppendMap k v) (k, v) where
    base (k, v) = AppendMap $ M.singleton k v

--
newtype List a = List { list :: [a] } 

deriving instance Show a => Show (List a)
deriving instance Eq a => Eq (List a)

instance Semigroup a => Semigroup (List a) where
    l1 <> l2 = List $ foldl1 (<>) <$> transpose [list l1, list l2]

instance Monoid a => Monoid (List a) where
    mempty = List $ repeat mempty

instance JoinSemilattice a => JoinSemilattice (List a) where
instance BoundedJoinSemilattice a => BoundedJoinSemilattice (List a) where

-- 
instance (JoinSemilattice a, JoinSemilattice b) => JoinSemilattice (a, b)
instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c) => JoinSemilattice (a, b, c)
instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c, JoinSemilattice d) => JoinSemilattice (a, b, c, d)

instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b) => BoundedJoinSemilattice (a, b)
instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b, BoundedJoinSemilattice c) => BoundedJoinSemilattice (a, b, c)
instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b, BoundedJoinSemilattice c, BoundedJoinSemilattice d) => BoundedJoinSemilattice (a, b, c, d)
--- and so on...
