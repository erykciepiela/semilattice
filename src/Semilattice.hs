module Semilattice (
    JoinSemilattice(..),
    BoundedJoinSemilattice(..),
    NestedSemilattice(..),
    en,
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
    Based(..),
    -- | Primitive bjsconcat semilattices 
    Increasing(..),
    propagateIncrease,
    propagateIncrease2,
    Decreasing(..),
    propagateDecrease,
    Same(..),
    propagateSame,
    Growing(..),
    propagateGrowth,
    Shrinking(..),
    propagateShrink,
    -- | Higher-kinded bjsconcat semilattices
    propagateMap,
    propagateMapEntry,
    propagateListElement
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

class BoundedJoinSemilattice n => NestedSemilattice n where
    enrich :: n -> n -> n
    strip :: n -> n -> n -- ?

instance (Ord k, BoundedJoinSemilattice s) => NestedSemilattice (M.Map k s) where
    enrich = M.intersectionWith (\/)
    strip = M.intersectionWith (/\)

instance (NestedSemilattice a, NestedSemilattice b) => NestedSemilattice (a, b) where
    enrich (a, b) (a', b') = (enrich a a', enrich b b')
    strip (a, b) (a', b') = (strip a a', strip b b')

en ::(NestedSemilattice s, Based s b) => b -> s -> s
en b = enrich (jirelement b)

push ::(JoinSemilattice s, Based s b) => b -> s -> s
push b = (\/ jirelement b)

pull ::(JoinSemilattice s, Based s b) => b -> s -> s
pull b = (/\ jirelement b)

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
    jirelement :: b -> s
    -- reduce :: s -> Either s b

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
newtype Growing a = Growing { growing :: Set a }

deriving instance Eq a => Eq (Growing a)
deriving instance Show a => Show (Growing a)
deriving instance Ord a => Ord (Growing a)

instance Ord a => Semigroup (Growing a) where
    s1 <> s2 = Growing $ S.union (growing s1) (growing s2)

instance Ord a => Monoid (Growing a) where
    mempty = Growing $ mempty

instance Ord a => JoinSemilattice (Growing a) where
    (\/) = (<>)
    Growing s1 /\ Growing s2 = Growing $ S.intersection s1 s2

instance Ord a => BoundedJoinSemilattice (Growing a) where
    bottom = mempty

instance Ord a => Based (Growing a) a where
    jirelement = Growing . S.singleton

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
    Shrinking s1 /\ Shrinking s2 = Shrinking $ S.union s1 s2

instance (Ord a, Enum a, Bounded a) => BoundedJoinSemilattice (Shrinking a) where
    bottom = mempty

instance (Ord a, Enum a, Bounded a) => Based (Shrinking a) a where
    jirelement a = Shrinking $ S.delete a (S.fromList $ enumFromTo minBound maxBound)

propagateShrink :: (Ord a, Ord b) => (a -> b) -> Shrinking a -> Shrinking b
propagateShrink f = Shrinking . S.map f . shrinking

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
instance (Ord k, JoinSemilattice v) => JoinSemilattice (M.Map k v) where
    (\/) = M.unionWith (\/)
    (/\) = M.intersectionWith (/\)

instance (Ord k, BoundedJoinSemilattice v) => BoundedJoinSemilattice (M.Map k v) where
    bottom = mempty

instance (Ord k, BoundedJoinSemilattice v) => Based (M.Map k v) (k, v) where
    jirelement (k, v) = M.singleton k v

propagateMap :: (Ord k, Ord k', JoinSemilattice v) => (v -> v -> v) -- | must be monotone
    -> (k -> k') -> M.Map k v -> M.Map k' v
propagateMap = M.mapKeysWith

propagateMapEntry :: (Ord k, BoundedJoinSemilattice s) => k -> M.Map k s -> s
propagateMapEntry k m = fromMaybe bottom $ M.lookup k m

propagateMapKeys :: (Ord k, BoundedJoinSemilattice s) => M.Map k s -> Growing k
propagateMapKeys = Growing . M.keysSet 

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
    E :: (Ord s, BoundedJoinSemilattice s) => Growing s -> E s

pHomo :: (BoundedJoinSemilattice a) => (a -> b) -> Growing a -> b
pHomo f g = f $ join g

pMono :: (BoundedJoinSemilattice a, BoundedJoinSemilattice b, Ord b) => (a -> b) -> Growing a -> b
pMono f g = bjsconcat $ S.map f (Semilattice.all g)

join :: (BoundedJoinSemilattice s) => Growing s -> s
join (Growing ss) = bjsconcat ss

all :: (BoundedJoinSemilattice s) => Growing s -> S.Set s
all (Growing ss) = ss


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
--     extract (E (Growing ss)) = bjsconcat ss
--     duplicate (E (Growing ss)) = E $ Growing $ S.map (\s -> E (Growing (S.singleton s))) ss
