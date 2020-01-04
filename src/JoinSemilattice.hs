module JoinSemilattice (
    JoinSemilattice,
    (+>),
    (<+),
    (<<+),
    (+>>),
    (<+>),
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
import Data.IntMap.Strict

class (Eq s, Monoid s) => JoinSemilattice s where
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

-- 
instance JoinSemilattice ()

instance (Ord a, Bounded a) => JoinSemilattice (Max a)

instance (Ord a, Bounded a) => JoinSemilattice (Min a)

instance JoinSemilattice All

instance JoinSemilattice Any

instance JoinSemilattice (Proxy a)

-- | If @a@ is Ord and Bounded and we know it increases in time.
-- | Equivalent to Max.
newtype Increasing a = Increasing { increasing :: a }

instance Ord a => Semigroup (Increasing a) where
    (Increasing a) <> (Increasing b) = Increasing (Prelude.max a b)

instance (Ord a, Bounded a) => Monoid (Increasing a) where
    mempty = Increasing minBound

deriving instance Eq a => Eq (Increasing a)

instance (Ord a, Bounded a) => JoinSemilattice (Increasing a)

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

instance (Ord a, Bounded a) => JoinSemilattice (Decreasing a)

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

propagateGrowth :: (Ord a, Ord b) => (a -> b) -> Growing a -> Growing b
propagateGrowth f = Growing . S.map f . growing

-- | If @a@ is Ord and we know we get fewer of them over time.
newtype Shrinking a = Shrinking { shrinking :: Set a }

deriving instance Eq a => Eq (Shrinking a)

instance Ord a => Semigroup (Shrinking a) where
    s1 <> s2 = Shrinking $ S.intersection (shrinking s1) (shrinking s2)

instance (Ord a, Enum a, Bounded a) => Monoid (Shrinking a) where
    mempty = Shrinking $ S.fromList $ enumFromTo minBound maxBound

instance (Ord a, Enum a, Bounded a) => JoinSemilattice (Shrinking a)

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

propagateSame :: (Ord a, Ord b) => (a -> b) -> Same a -> Same b
propagateSame f Unknown = Unknown
propagateSame f (Unambiguous a) = Unambiguous (f a)
propagateSame f (Ambiguous as) = Ambiguous (S.map f as)

-- higher order join semilattices

--
instance JoinSemilattice a => JoinSemilattice (Identity a)

--
instance (Ord k, JoinSemilattice v) => JoinSemilattice (AppendMap k v)

--
newtype List a = List { list :: [a] } 

deriving instance Show a => Show (List a)
deriving instance Eq a => Eq (List a)

instance Semigroup a => Semigroup (List a) where
    l1 <> l2 = List $ foldl1 (<>) <$> transpose [list l1, list l2]

instance Monoid a => Monoid (List a) where
    mempty = List $ repeat mempty

instance JoinSemilattice a => JoinSemilattice (List a) where

-- 
instance (JoinSemilattice a, JoinSemilattice b) => JoinSemilattice (a, b)
instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c) => JoinSemilattice (a, b, c)
instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c, JoinSemilattice d) => JoinSemilattice (a, b, c, d)
--- and so on...
