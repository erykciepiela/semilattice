module JoinSemilattice (
    JoinSemilattice,
    (+>),
    (<+),
    (<<+),
    (+>>),
    (<+>),
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
    List,
    Map,
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

-- 
instance JoinSemilattice Void

instance JoinSemilattice ()

instance Ord a => JoinSemilattice (Max a)

instance Ord a => JoinSemilattice (Min a)

instance JoinSemilattice All

instance JoinSemilattice Any

instance JoinSemilattice (Proxy a)

-- | If @a@ is Ord and we know it increases in time.
-- | Equivalent to Max.
newtype Increasing a = Increasing { increasing :: a }

instance Ord a => Semigroup (Increasing a) where
    (Increasing a) <> (Increasing b) = Increasing (Prelude.max a b)

instance (Ord a, Bounded a) => Monoid (Increasing a) where
    mempty = Increasing minBound

deriving instance Eq a => Eq (Increasing a)

instance Ord a => JoinSemilattice (Increasing a)

propagateIncrease :: (a -> b) -> Increasing a -> Increasing b
propagateIncrease f (Increasing a) = Increasing (f a) -- f must be monotone

-- | If @a@ is Ord and we know it decreases in time.
-- | Equivalent to Min.
newtype Decreasing a = Decreasing { decreasing :: a }

instance Ord a => Semigroup (Decreasing a) where
    (Decreasing a) <> (Decreasing b) = Decreasing (Prelude.min a b)

instance (Ord a, Bounded a) => Monoid (Decreasing a) where
    mempty = Decreasing maxBound

deriving instance Eq a => Eq (Decreasing a)

instance Ord a => JoinSemilattice (Decreasing a)

propagateDecrease :: (a -> b) -> Decreasing a -> Decreasing b
propagateDecrease f (Decreasing a) = Decreasing (f a) -- f must be counter-monotone

-- | If @a@ is Ord and we know we get more of them over time.
newtype Growing a = Growing { growing :: Set a }

deriving instance Eq a => Eq (Growing a)
deriving instance Show a => Show (Growing a)

instance Ord a => Semigroup (Growing a) where
    s1 <> s2 = Growing $ S.union (growing s1) (growing s2)

instance Ord a => JoinSemilattice (Growing a)

propagateGrowth :: (Ord a, Ord b) => (a -> b) -> Growing a -> Growing b
propagateGrowth f = Growing . S.map f . growing

-- | If @a@ is Ord and we know we get fewer of them over time.
newtype Shrinking a = Shrinking { shrinking :: Set a }

deriving instance Eq a => Eq (Shrinking a)

instance Ord a => Semigroup (Shrinking a) where
    s1 <> s2 = Shrinking $ S.intersection (shrinking s1) (shrinking s2)

instance Ord a => JoinSemilattice (Shrinking a)

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
newtype List a = List { list :: [a] } 

deriving instance Show a => Show (List a)
deriving instance Eq a => Eq (List a)

instance Semigroup a => Semigroup (List a) where
    l1 <> l2 = List $ foldl1 (<>) <$> transpose [list l1, list l2]

instance JoinSemilattice a => JoinSemilattice (List a) where


    



-- product join semilattice
instance (JoinSemilattice a, JoinSemilattice b) => JoinSemilattice (a, b)
instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c) => JoinSemilattice (a, b, c)


-- 
type Map k v = AppendMap k v

instance (Ord k, JoinSemilattice v) => JoinSemilattice (Map k v)


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
