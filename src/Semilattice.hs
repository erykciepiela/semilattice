module Semilattice (
    JoinSemilattice(..),
    BoundedJoinSemilattice(..),
    (+>),
    (<+),
    (<<+),
    (+>>),
    (<+>),
    bjsconcat,
    bjsscan,
    ascends,
    ascendsTowards,
    ascendsTo,    
    isDescending,
    Homo(..),
    Based(..),
    bconcat,
    -- | Primitive bjsconcat semilattices 
    Increasing(..),
    propagateIncrease,
    propagateIncrease2,
    Decreasing(..),
    propagateDecrease,
    Same(..),
    propagateSame,
    GrowingSet(..),
    propagateGrowth,
    ShrinkingSet(..),
    propagateShrink,
    -- | Higher-kinded bjsconcat semilattices
    GrowingMap(..),
    propagateMap,
    propagateMapEntry,
    propagateListElement,
    --
    propagateFst,
    propagateSnd
) where

import Prelude hiding (id, (.))
import Data.Set as S
import Data.Semigroup
import qualified Data.Map as M
import Data.List as L
import Control.Category
import Data.Proxy
import Data.Functor.Identity
import Data.Void
import Data.Maybe
import Data.IORef
import Control.Comonad
import Data.String

class JoinSemilattice s where
    -- a \/ (b  \/ c) = (a \/ n) \/ c - associativity
    -- a \/ b = b \/ a - commutativity, saves us from out of order messages problem
    -- a \/ a = a idempotence, saves us from exactly-once delivery guarantee problem
    -- a \/ b >= a 
    -- a \/ b >= b 
    (\/) :: s -> s -> s
    -- a /\ b <= a 
    -- a /\ b <= b 
    (/\) :: s -> s -> s

class JoinSemilattice s => BoundedJoinSemilattice s where
    bottom :: s

bjsconcatS :: (Ord s, BoundedJoinSemilattice s) => S.Set s -> s
bjsconcatS = S.foldr (\/) bottom

bjsconcat :: (Foldable f, BoundedJoinSemilattice s) => f s -> s
bjsconcat = Prelude.foldr (\/) bottom
-- if f s is bounded semilattice then it's a propagator

bjsscan :: (BoundedJoinSemilattice s) => [s] -> [s]
bjsscan = scanl' (\/) bottom

bjsconcat'' :: (Foldable f, BoundedJoinSemilattice s, BoundedJoinSemilattice (f s)) => f s -> s
bjsconcat'' = Prelude.foldr (\/) bottom

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

ascends :: (Eq s, BoundedJoinSemilattice s) => [s] -> Bool
ascends ss = let ss' = bjsscan ss in isAscending ss'
    where
        isAscending :: (Eq s, BoundedJoinSemilattice s) => [s] -> Bool
        isAscending [] = True
        isAscending [s] = True
        isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest

ascendsTowards :: (Eq s, BoundedJoinSemilattice s) => [s] -> s -> Bool
ascendsTowards [] final = final == bottom
ascendsTowards ss final = let ss' = bjsscan ss in isAscending ss' && L.all (<+ final) ss'
    where
        isAscending :: (Eq s, BoundedJoinSemilattice s) => [s] -> Bool
        isAscending [] = True
        isAscending [s] = True
        isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest

ascendsTo :: (Eq s, BoundedJoinSemilattice s) => [s] -> s -> Bool
ascendsTo [] final = final == bottom
ascendsTo ss final = let ss' = bjsscan ss in isAscending ss' && L.all (<+ final) ss' && last ss' == final
    where
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
    -- join-irreducible element
    jirelement :: b -> s

bconcat :: Based s b => [b] -> s
bconcat bs = bjsconcat $ jirelement <$> bs

--
newtype Homo a b = Homo { homo :: a -> b }

instance Category Homo where
    id = Homo id
    h1 . h2 = Homo $ homo h1 . homo h2 

-- 
instance JoinSemilattice () where
    (\/) = (<>)
    (/\) = (<>)

instance BoundedJoinSemilattice () where
    bottom = mempty

instance Based () () where
    jirelement = id

--
instance Ord a => JoinSemilattice (Max a) where
    (\/) = (<>)
    Max a1 /\ Max a2 = Max $ min a1 a2

instance (Ord a, Bounded a) => BoundedJoinSemilattice (Max a) where
    bottom = mempty

instance (Ord a, Bounded a) => Based (Max a) a where
    jirelement = Max

--
instance Ord a => JoinSemilattice (Min a) where
    (\/) = (<>)
    Min a1 /\ Min a2 = Min $ max a1 a2

instance (Ord a, Bounded a) => BoundedJoinSemilattice (Min a) where
    bottom = mempty

instance (Ord a, Bounded a) => Based (Min a) a where
    jirelement = Min

--
instance JoinSemilattice All where
    (\/) = (<>)
    All True /\ All True = All True
    _ /\ _ = All False

instance BoundedJoinSemilattice All  where
    bottom = mempty

instance Based All Bool where
    jirelement = All

--
instance JoinSemilattice Any where
    (\/) = (<>)
    Any True /\ Any True = Any True
    _ /\ _ = Any False

instance BoundedJoinSemilattice Any  where
    bottom = mempty

instance Based Any Bool where
    jirelement = Any


--
instance JoinSemilattice (Proxy a) where
    (\/) = (<>)
    (/\) = (<>)

instance BoundedJoinSemilattice (Proxy a) where
    bottom = mempty

instance Based (Proxy a) () where
    jirelement _ = Proxy

-- | If @a@ is Ord and Bounded and we know it increases in time.
-- | Equivalent to Max.
newtype Increasing a = Increasing a -- { increasing :: a }

instance Num a => Num (Increasing a) where
    fromInteger = Increasing . fromInteger

-- instance IsString a => IsString (Increasing a) where
--     fromString = Increasing . fromString

-- instance Num a => Num (Increasing a) where

deriving instance Show a => Show (Increasing a)

instance Ord a => Semigroup (Increasing a) where
    (Increasing a) <> (Increasing b) = Increasing (Prelude.max a b)

instance (Ord a, Bounded a) => Monoid (Increasing a) where
    mempty = Increasing minBound

deriving instance Eq a => Eq (Increasing a)

instance Ord a => JoinSemilattice (Increasing a) where
    (\/) = (<>)
    Increasing a1 /\ Increasing a2 = Increasing $ min a1 a2
    
instance (Ord a, Bounded a) => BoundedJoinSemilattice (Increasing a) where
    bottom = mempty

instance (Ord a, Bounded a) => Based (Increasing a) a where
    jirelement = Increasing

propagateIncrease :: (a -> b) -> Increasing a -> Increasing b
propagateIncrease f (Increasing a) = Increasing (f a) -- f must be monotone!
-- if f is counter-monotine - inverse
-- f (Inc 3 \/ Inc 5) = f (Inc 3) \/ f (Inc 5)
-- f (Inc 5) = (Inc -3) \/ (Inc -5)
-- Inc -5 = Inc -3
-- if f is not monotine - (+1)
-- f (Inc 3 \/ Inc 5) = f (Inc 3) \/ f (Inc 5)
-- f (Inc 5) = (Inc 4) \/ (Inc 6)
-- Inc 6 = Inc 6

propagateIncrease2 :: (a -> b -> c) -> Increasing a -> Increasing b -> Increasing c
propagateIncrease2 f (Increasing a) (Increasing b) = Increasing (f a b) -- f must be monotone!
-- f (I 2 \/ I 5) (I 3 \/ I 4) = f (I 2) (I 3) \/ f (I 5) (I 4) 
-- f (I 5) (I 4) = (I 2) \/ (I 3) \/ (I 5) \/ (I 4) 
-- (I 5) \/ (I 4) = (I 2) \/ (I 3) \/ (I 5) \/ (I 4) 
-- I 5 = I 5

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
    Decreasing a1 /\ Decreasing a2 = Decreasing $ max a1 a2

instance (Ord a, Bounded a) => BoundedJoinSemilattice (Decreasing a) where
    bottom = mempty

instance (Ord a, Bounded a) => Based (Decreasing a) a where
    jirelement = Decreasing

propagateDecrease :: (a -> b) -> Decreasing a -> Decreasing b
propagateDecrease f (Decreasing a) = Decreasing (f a) -- f must be monotone!
-- if f is counter-monotone (e.g. inverse) then propagateDecrease is not homomorphic
-- f (Dec 3 \/ Dec 5) = f (Dec 3) \/ f (Dec 5)
-- f (Dec 3) = (Dec -3) \/ (Dec -5)
-- Dec -3 = Dec -5
-- if f is not monotine (e.g.(+1)) then then propagateDecrease is homomorphic
-- f (Dec 3 \/ Dec 5) = f (Dec 3) \/ f (Dec 5)
-- f (Dec 3) = (Dec 4) \/ (Dec 6)
-- Dec 4 = Dec 4

-- | If @a@ is Ord and we know we get more of them over time.
newtype GrowingSet a = GrowingSet { growing :: Set a }

deriving instance Eq a => Eq (GrowingSet a)
deriving instance Show a => Show (GrowingSet a)
deriving instance Ord a => Ord (GrowingSet a)

instance Ord a => Semigroup (GrowingSet a) where
    s1 <> s2 = GrowingSet $ S.union (growing s1) (growing s2)

instance Ord a => Monoid (GrowingSet a) where
    mempty = GrowingSet $ mempty

instance Ord a => JoinSemilattice (GrowingSet a) where
    (\/) = (<>)
    GrowingSet s1 /\ GrowingSet s2 = GrowingSet $ S.intersection s1 s2

instance Ord a => BoundedJoinSemilattice (GrowingSet a) where
    bottom = mempty

instance Ord a => Based (GrowingSet a) a where
    jirelement = GrowingSet . S.singleton

propagateGrowth :: (Ord a, Ord b) => (a -> b) -> GrowingSet a -> GrowingSet b
propagateGrowth f = GrowingSet . S.map f . growing

-- | If @a@ is Ord and we know we get fewer of them over time.
newtype ShrinkingSet a = ShrinkingSet { shrinking :: Set a }

deriving instance Eq a => Eq (ShrinkingSet a)

instance Ord a => Semigroup (ShrinkingSet a) where
    s1 <> s2 = ShrinkingSet $ S.intersection (shrinking s1) (shrinking s2)

instance (Ord a, Enum a, Bounded a) => Monoid (ShrinkingSet a) where
    mempty = ShrinkingSet $ S.fromList $ enumFromTo minBound maxBound

instance Ord a => JoinSemilattice (ShrinkingSet a) where
    (\/) = (<>)
    ShrinkingSet s1 /\ ShrinkingSet s2 = ShrinkingSet $ S.union s1 s2

instance (Ord a, Enum a, Bounded a) => BoundedJoinSemilattice (ShrinkingSet a) where
    bottom = mempty

instance (Ord a, Enum a, Bounded a) => Based (ShrinkingSet a) a where
    jirelement a = ShrinkingSet $ S.delete a (S.fromList $ enumFromTo minBound maxBound)

propagateShrink :: (Ord a, Ord b) => (a -> b) -> ShrinkingSet a -> ShrinkingSet b
propagateShrink f = ShrinkingSet . S.map f . shrinking

-- | If @a@ is Ord and we know we it should stay the same over time.
-- newtype Same a = Same { same :: Either [a] a }
data Same a = Unknown | Unambiguous a | Ambiguous (Set a)

deriving instance Eq a => Eq (Same a)
deriving instance Show a => Show (Same a)

instance IsString a => IsString (Same a) where
    fromString = Unambiguous . fromString

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
    Unknown /\ p = Unknown
    p /\ Unknown = Unknown
    Ambiguous as /\ p@(Unambiguous a) = p
    p@(Unambiguous a) /\ Ambiguous as = p
    Ambiguous as1 /\ Ambiguous as2 = Ambiguous (S.intersection as1 as2) -- ?
    p@(Unambiguous a1) /\ (Unambiguous a2)
        | a1 == a2 = p
        | otherwise = Unknown

instance Ord a => BoundedJoinSemilattice (Same a) where
    bottom = mempty

instance Ord a => Based (Same a) a where
    jirelement = Unambiguous


propagateSame :: (Ord a, Ord b) => (a -> b) -> Same a -> Same b
propagateSame f Unknown = Unknown
propagateSame f (Unambiguous a) = Unambiguous (f a)
propagateSame f (Ambiguous as) = Ambiguous (S.map f as)

-- higher kinded bjsconcat semilattices

--
instance JoinSemilattice a => JoinSemilattice (Identity a) where
    Identity a1 \/ Identity a2 = Identity $ a1 \/ a2
    Identity a1 /\ Identity a2 = Identity $ a1 /\ a2

instance BoundedJoinSemilattice a => BoundedJoinSemilattice (Identity a) where
    bottom = bottom

instance Based a b => Based (Identity a) b where
    jirelement = Identity . jirelement

--
newtype GrowingMap k v = GrowingMap { growingMap :: M.Map k v}

deriving instance (Eq k, Eq v) => Eq (GrowingMap k v)
deriving instance (Show k, Show v) => Show (GrowingMap k v)

instance (Ord k, JoinSemilattice v) => JoinSemilattice (GrowingMap k v) where
    GrowingMap m1 \/ GrowingMap m2 = GrowingMap $ M.unionWith (\/) m1 m2
    GrowingMap m1 /\ GrowingMap m2 = GrowingMap $ M.intersectionWith (/\) m1 m2

instance (Ord k, BoundedJoinSemilattice v) => BoundedJoinSemilattice (GrowingMap k v) where
    bottom = GrowingMap mempty

instance (Ord k, BoundedJoinSemilattice v) => Based (GrowingMap k v) (k, v) where
    jirelement (k, v) = GrowingMap $ M.singleton k v

propagateMap :: (Ord k, BoundedJoinSemilattice s, BoundedJoinSemilattice s') => Homo s s' -> Homo (GrowingMap k s) (GrowingMap k s')
propagateMap h = Homo $ GrowingMap . fmap (homo h) . growingMap

propagateMapEntry :: (Ord k, BoundedJoinSemilattice s) => k -> Homo (GrowingMap k s) s
propagateMapEntry k = Homo $ fromMaybe bottom . M.lookup k . growingMap

propagateMapKeys :: (Ord k, BoundedJoinSemilattice s) => GrowingMap k s -> GrowingSet k
propagateMapKeys = GrowingSet . M.keysSet . growingMap



--
instance JoinSemilattice a => JoinSemilattice [a] where
    l1 \/ l2 = foldl1 (\/) <$> transpose [l1, l2]
    l1 /\ l2 = foldl1 (/\) <$> transpose [l1, l2]

instance BoundedJoinSemilattice a => BoundedJoinSemilattice [a] where
    bottom = mempty

instance Based a b => Based [a] (Int, b) where
    jirelement (n, b) = replicate n bottom <> [jirelement b]


propagateListElement :: BoundedJoinSemilattice a => Int -> [a] -> a
propagateListElement i l 
  | i >= length l = bottom
  | otherwise = l !! i

-- 
instance (JoinSemilattice a, JoinSemilattice b) => JoinSemilattice (a, b) where
    (a1, b1) \/ (a2, b2) = (a1 \/ a2, b1 \/ b2)
    (a1, b1) /\ (a2, b2) = (a1 /\ a2, b1 /\ b2)

propagateFst :: (JoinSemilattice a, JoinSemilattice b) => Homo (a, b) a
propagateFst = Homo fst

propagateSnd :: (JoinSemilattice a, JoinSemilattice b) => Homo (a, b) b
propagateSnd = Homo snd

instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b) => BoundedJoinSemilattice (a, b) where
    bottom = (bottom, bottom)

instance (Based a b, Based c d) => Based (a, c) (Either b d) where
    jirelement (Left b) = (jirelement b, bottom) 
    jirelement (Right d) = (bottom, jirelement d) 

--
instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c) => JoinSemilattice (a, b, c) where
    (a1, b1, c1) \/ (a2, b2, c2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2)
    (a1, b1, c1) /\ (a2, b2, c2) = (a1 /\ a2, b1 /\ b2, c1 /\ c2)

instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b, BoundedJoinSemilattice c) => BoundedJoinSemilattice (a, b, c) where
    bottom = (bottom, bottom, bottom)

instance (Based a b, Based c d, Based e f) => Based (a, c, e) (b, d, f) where
    jirelement (b, d, f) = (jirelement b, jirelement d, jirelement f) 

--
instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c, JoinSemilattice d) => JoinSemilattice (a, b, c, d) where
    (a1, b1, c1, d1) \/ (a2, b2, c2, d2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2, d1 \/ d2)
    (a1, b1, c1, d1) /\ (a2, b2, c2, d2) = (a1 /\ a2, b1 /\ b2, c1 /\ c2, d1 /\ d2)

instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b, BoundedJoinSemilattice c, BoundedJoinSemilattice d) => BoundedJoinSemilattice (a, b, c, d) where
    bottom = (bottom, bottom, bottom, bottom)

instance (Based a b, Based c d, Based e f, Based g h) => Based (a, c, e, g) (b, d, f, h) where
    jirelement (b, d, f, h) = (jirelement b, jirelement d, jirelement f, jirelement h) 

-- and so on...

--
instance (JoinSemilattice a, JoinSemilattice b) => JoinSemilattice (Either a b) where
    Left a1 \/ Left a2 = Left (a1 \/ a2)
    Right b1 \/ Right b2 = Right (b1 \/ b2)
    Left _ \/ r@(Right _) = r
    r@(Right _) \/ Left _ = r
    Left a1 /\ Left a2 = Left (a1 /\ a2)
    Right b1 /\ Right b2 = Right (b1 /\ b2)
    r@(Left _) /\ Right _ = r
    Right _ /\ r@(Left _) = r

instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b) => BoundedJoinSemilattice (Either a b) where
    bottom = Left bottom

instance (Based a b, Based c d) => Based (Either a c) (Either b d) where
    jirelement (Left b) = Left $ jirelement b
    jirelement (Right d) = Right $ jirelement d



-- | More on homomorphisms
-- @f@ is homomorphisms if and only if @f (x \/ y) = f x \/ f y@
-- if @f@ is homomorphism then @f@ is monotone
-- x \/ y +> x and f (x \/ y) = f x \/ f y +> f x
-- x \/ y +> y and f (x \/ y) = f x \/ f y +> f y
-- Let's assume we deal with a stream of arriving @a@s: a1, a2, ..., an.
-- The order of arrival does not have to reflect occurrence order.
-- Arrived values can be duplicated.
-- f (a1 \/ a2 \/ ... \/ an) = f a1 \/ f a2 \/ ... \/ f an
-- f :: a -> b
-- a -> (b -> b)

propagateMono :: (BoundedJoinSemilattice a, BoundedJoinSemilattice b, Foldable t, Functor t) => (a -> b) -> t a -> b
propagateMono f as =  bjsconcat $ f <$> as
-- 
-- if f is homomorphism:
-- propagateMono f [a1, a2]
-- = bjsconcat $ [f a1, f a2]
-- = f a1 \/ f a2
-- = f (a1 \/ a2) -- as f is monomorphism
-- = f (bjsconcat [a1, a2])
propagateHomo :: (BoundedJoinSemilattice a, BoundedJoinSemilattice b, Foldable t) => (a -> b) -> t a -> b
propagateHomo f as = f $ bjsconcat as

--

data E s where
    E :: (Ord s, BoundedJoinSemilattice s) => GrowingSet s -> E s

pHomo :: (BoundedJoinSemilattice a) => (a -> b) -> GrowingSet a -> b
pHomo f g = f $ join g

pMono :: (BoundedJoinSemilattice a, BoundedJoinSemilattice b, Ord b) => (a -> b) -> GrowingSet a -> b
pMono f g = bjsconcat $ S.map f (Semilattice.all g)

join :: (BoundedJoinSemilattice s) => GrowingSet s -> s
join (GrowingSet ss) = bjsconcat ss

all :: (BoundedJoinSemilattice s) => GrowingSet s -> S.Set s
all (GrowingSet ss) = ss


-- instance Eq (E s) where
--     E g1 == E g2 = g1 == g2

-- instance Ord (E s) where
--     compare (E g1) (E g2) = compare g1 g2

-- instance Ord s => JoinSemilattice (E s) where
--     (E g1) \/ (E g2) = E $ g1 \/ g2

-- instance (BoundedJoinSemilattice s, Ord s) => BoundedJoinSemilattice (E s) where
--     bottom = E bottom

-- instance Functor E where
--     fmap = undefined 

-- instance Comonad E where
--     extract (E (GrowingSet ss)) = bjsconcat ss
--     duplicate (E (GrowingSet ss)) = E $ GrowingSet $ S.map (\s -> E (GrowingSet (S.singleton s))) ss
