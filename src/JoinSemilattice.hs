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
    Growing(..),
    propagateGrowth,
    Shrinking(..),
    propagateShrink,
    List,
    Map,
    Promise(..),
    Value(..),
    getValue,
    Data.Semigroup.Max,
    Monotone(..),
    propagate,
    SemiLat(..),
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

--
data Value a = Value a | Contradiction
deriving instance (Eq a) => Eq (Value a)
deriving instance (Show a) => Show (Value a)

instance Functor Value where
    fmap _ Contradiction = Contradiction
    fmap f (Value a) = Value (f a)

instance Eq a => Semigroup (Value a) where
    Contradiction <> _ = Contradiction
    _ <> Contradiction = Contradiction
    v@(Value a1) <> (Value a2)
        | a1 == a2 = v
        | otherwise = Contradiction

instance Eq a => JoinSemilattice (Value a)

getValue :: Value a -> Maybe a
getValue (Value a) = Just a
getValue Contradiction = Nothing



-- higher order join semilattices
newtype List a = List { list :: [a] } 

deriving instance Show a => Show (List a)
deriving instance Eq a => Eq (List a)

instance Semigroup a => Semigroup (List a) where
    l1 <> l2 = List $ foldl1 (<>) <$> transpose [list l1, list l2]

instance JoinSemilattice a => JoinSemilattice (List a) where


    


-- (no value - a value - contradiction) join semilattice
data Promise a = None | Promised a | Contradicted 

deriving instance (Eq a) => Eq (Promise a)
deriving instance (Show a) => Show (Promise a)

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
