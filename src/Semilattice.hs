module Semilattice (
    Semilattice(..),
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
    isEventuallyConsistent,    
    isDescending,
    isAscending,
    isAscendingTowards,
    collect,
    Homo(..),
    propagateHomo,
    propagatedHomo,
    composeHomo,
    decomposeHomo,
    Mono(..),
    propagateMono,
    propagatedMono,
    Dual(..),
    dmapToLattice,
    dmapToSets,
    Proc(..),
    runProc,
    -- | Primitive bjsconcat semilattices 
    Increasing(..),
    propagateIncrease,
    propagateIncrease2,
    Decreasing(..),
    propagateDecrease,
    Same(..),
    propagateSame,
    -- | Higher-kinded bjsconcat semilattices
    propagateMap,
    propagateMapEntry,
    propagateMapKeys,
    propagateMapValues,
    --
    propagateFst,
    propagateSnd
) where

import Prelude hiding (id, (.))
import Data.Set as S
import qualified Data.Map as M
import Data.List as L
import Control.Category
import Data.Proxy
import Data.Functor.Identity
import Data.Void
import Data.Maybe
import Data.String

-- | Partial order
-- | (Eq is discrete order)
class Eq p => PartialOrd p where
    -- a +> a -- reflexivity
    -- a +> b +> c => a +> c - transitivity
    -- a +> b and b +> a => a == b - antisymmetry
    (+>) :: p -> p -> Bool -- minimal definition
    (<+) :: p -> p -> Bool
    (<+) = flip (+>)
    (<+>) :: p -> p -> Bool -- are two ps comparable
    a <+> b = a +> b || b +> a
    (>+<) :: p -> p -> Bool -- are two ps not comparable
    a >+< b = not $ a <+> b
    (+>>) :: p -> p -> Bool
    a +>> b = a +> b && (a /= b)
    (<<+) :: p -> p -> Bool
    (<<+) = flip (+>>)

class PartialOrd s => Semilattice s where
    -- a \/ (b  \/ c) = (a \/ b) \/ c - associativity
    -- a \/ b = b \/ a - commutativity
    -- a \/ a = a idempotence
    -- a \/ b +> a
    -- a \/ b +> b
    (\/) :: s -> s -> s
    -- a /\ (b  /\ c) = (a /\ b) /\ c - associativity
    -- a /\ b = b /\ a - commutativity
    -- a /\ a = a idempotence
    -- a /\ b <+ a
    -- a /\ b <+ b
    (/\) :: s -> s -> s
    -- if s is also Bounded then
    -- a \/ minBound = a = minBound \/ a 
    -- a /\ maxBound = a = maxBound /\ a 

bjsconcatS :: (Ord s, Semilattice s, Bounded s) => S.Set s -> s
bjsconcatS = S.foldr (\/) minBound

bjsconcat :: (Foldable f, Semilattice s, Bounded s) => f s -> s
bjsconcat = Prelude.foldr (\/) minBound
-- if f s is bounded semilattice then it's a propagator

bjsscan :: (Semilattice s, Bounded s) => [s] -> [s]
bjsscan = scanl' (\/) minBound

bjsconcat'' :: (Foldable f, Semilattice s, Bounded s, Semilattice (f s), Bounded (f s)) => f s -> s
bjsconcat'' = Prelude.foldr (\/) minBound


ascends :: (Eq s, Semilattice s, Bounded s) => [s] -> Bool
ascends ss = let ss' = bjsscan ss in isAscending ss'
    where
        isAscending :: (Eq s, Semilattice s, Bounded s) => [s] -> Bool
        isAscending [] = True
        isAscending [s] = True
        isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest

ascendsTowards :: (Eq s, Semilattice s, Bounded s) => [s] -> s -> Bool
ascendsTowards [] final = final == minBound
ascendsTowards ss final = let ss' = bjsscan ss in isAscending ss' && L.all (<+ final) ss'

isAscending :: (Eq s, PartialOrd s) => [s] -> Bool
isAscending [] = True
isAscending [s] = True
isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest

isAscendingTowards :: (Eq s, PartialOrd s) => [s] -> s -> Bool
isAscendingTowards ss s = isAscending ss && last ss == s -- assuming ss not empty

ascendsTo :: (Eq s, Semilattice s, Bounded s) => [s] -> s -> Bool
ascendsTo [] final = final == minBound
ascendsTo ss final = let ss' = bjsscan ss in isAscending ss' && L.all (<+ final) ss' && last ss' == final
-- ascendsTo ss final = let ss' = bjsscan ss in last ss' == final
    where
        isAscending :: (Eq s, Semilattice s, Bounded s) => [s] -> Bool
        isAscending [] = True
        isAscending [s] = True
        isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest

isEventuallyConsistent :: (Eq s, Semilattice s, Bounded s) => [[s]] -> s -> Bool
isEventuallyConsistent [] final = final == minBound
isEventuallyConsistent ss final = ascendsTo (bjsconcat <$> ss) final

isDescending :: (Eq s, Semilattice s, Bounded s) => [s] -> Bool
isDescending [] = True
isDescending [s] = True
isDescending (s1:rest@(s2:_)) = s1 +> s2 && isDescending rest

--
newtype Homo a b = Homo { homo :: a -> b }

instance Category Homo where
    id = Homo id
    h1 . h2 = Homo $ homo h1 . homo h2 

decomposeHomo :: Dual s b => Homo s (Set b)
decomposeHomo = Homo $ decompose

composeHomo :: Dual s b => Homo (Set b) s
composeHomo = Homo $ compose

collect :: Ord a => [a] -> [Set a]
collect = scanl (\s a -> a `S.insert` s) mempty

propagateHomo :: (Semilattice b, Bounded b) => Homo a b -> [a] -> [b]
propagateHomo (Homo f) = scanl (\b a -> b \/ f a) minBound

propagatedHomo :: (Semilattice b, Bounded b) => [a] -> Homo a b -> [b]
propagatedHomo = flip propagateHomo

-- propagatedHomo' :: (Semilattice a, Bounded a, Semilattice b, Bounded b) => [[a]] -> Homo a b -> [b]
-- propagatedHomo' ass (Homo f) = scanl (\b a -> b \/ f a) minBound
--
newtype Mono a b = Mono { mono :: a -> b }

instance Category Mono where
    id = Mono id
    m1 . m2 = Mono $ mono m1 . mono m2 

propagateMono :: (Semilattice a, Bounded a, PartialOrd b) => Mono a b -> [a] -> [b]
propagateMono (Mono f) as = f <$> scanl (\/) minBound as 

propagatedMono :: (Semilattice a, Bounded a, PartialOrd b) => [a] -> Mono a b -> [b]
propagatedMono = flip propagateMono

data Proc a b = forall s. (Semilattice s, Bounded s) => Proc { phomo :: Homo a s, pf :: s -> b }

runProc :: Proc a b -> [a] -> [b]
runProc (Proc (Homo h) m) as = m <$> bjsscan (h <$> as)

instance Functor (Proc a) where
    fmap f (Proc h g) = Proc h (f . g)


instance Applicative (Proc a) where
    pure b = Proc foo (const b)
        where
            foo :: Homo a ()
            foo = Homo (const ())
    (Proc fh fm) <*> (Proc ah am) = Proc (Homo $ \i -> (homo fh i, homo ah i)) (\(fs, as) -> fm fs (am as))

procid :: (Semilattice a, Bounded a) => Proc a a
procid = Proc id id

procbimap :: Homo a' a -> (b -> b') -> Proc a b -> Proc a' b'
procbimap h m (Proc ph pm) = Proc (ph . h) (m . pm)

--
instance PartialOrd () where
    () +> () = True

instance Semilattice () where
    _ \/ _ = ()
    _ /\ _ = ()

-- instance Bounded () where -- in GHC.Enum

--
instance PartialOrd (Proxy a) where
    Proxy +> Proxy = True

instance Semilattice (Proxy a) where
    _ \/ _ = Proxy
    _ /\ _ = Proxy

-- instance Bounded (Proxy a) where -- in Data.Proxy

--
newtype Increasing a = Increasing { increasing :: a }

deriving instance Show a => Show (Increasing a)
deriving instance Eq a => Eq (Increasing a)

instance Ord a => PartialOrd (Increasing a) where
    (Increasing a) +> (Increasing b) = a >= b
    
instance Ord a => Semilattice (Increasing a) where
    (Increasing a) \/ (Increasing b) = Increasing (max a b)
    (Increasing a) /\ (Increasing b) = Increasing (min a b)

instance (Ord a, Bounded a) => Bounded (Increasing a) where
    minBound = Increasing minBound
    maxBound = Increasing maxBound

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

--
newtype Decreasing a = Decreasing { decreasing :: a }

deriving instance Show a => Show (Decreasing a)
deriving instance Eq a => Eq (Decreasing a)

instance Ord a => PartialOrd (Decreasing a) where
    Decreasing a +> Decreasing b = a <= b

instance Ord a => Semilattice (Decreasing a) where
    (Decreasing a) \/ (Decreasing b) = Decreasing (min a b)
    (Decreasing a) /\ (Decreasing b) = Decreasing (max a b)

instance (Ord a, Bounded a) => Bounded (Decreasing a) where
    minBound = Decreasing minBound
    maxBound = Decreasing maxBound

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

-- | If @a@ is Ord and we know we get more/less of them over time.
instance Ord a => PartialOrd (Set a) where
    (+>) = (>=)

instance Ord a => Semilattice (Set a) where
    (\/) = S.union
    (/\) = S.intersection

instance (Ord a, Enum a, Bounded a) => Bounded (Set a) where
    minBound = mempty
    maxBound = fromList [minBound..]

-- propagateGrowth :: (Ord a, Ord b) => (a -> b) -> Homo (GrowingSet a) (GrowingSet b)
-- propagateGrowth f = Homo $ GrowingSet . S.map f . growingSet

-- propagateSetSize :: Mono (GrowingSet a) (Increasing Int)
-- propagateSetSize = Mono $ Increasing . length . growingSet

--
data Same a = Unknown | Unambiguous a | Ambiguous (Set a)

deriving instance Show a => Show (Same a)
deriving instance Eq a => Eq (Same a)

instance Ord a => PartialOrd (Same a) where
    Unknown +> Unknown = True
    Unknown +> _ = False
    _ +> Unknown = True
    Unambiguous a1 +> Unambiguous a2 = a1 == a2
    Ambiguous s1 +> Ambiguous s2 = s1 >= s2
    Ambiguous s1 +> _ = True
    _ +> Ambiguous s2 = True

instance Ord a => Semilattice (Same a) where
    Unknown \/ p = p
    p \/ Unknown = p
    Ambiguous as \/ Unambiguous a = Ambiguous (S.insert a as) 
    Unambiguous a \/ Ambiguous as = Ambiguous (S.insert a as) 
    Ambiguous as1 \/ Ambiguous as2 = Ambiguous (S.union as1 as2)
    p@(Unambiguous a1) \/ (Unambiguous a2)
        | a1 == a2 = p
        | otherwise = Ambiguous (S.fromList [a1, a2])
    _ /\ _ = undefined 

instance (Enum a, Bounded a, Ord a) => Bounded (Same a) where
    minBound = Unknown
    maxBound = Ambiguous $ S.fromList [minBound..]

propagateSame :: (Ord a, Ord b) => (a -> b) -> Same a -> Same b
propagateSame f Unknown = Unknown
propagateSame f (Unambiguous a) = Unambiguous (f a)
propagateSame f (Ambiguous as) = Ambiguous (S.map f as)

-- higher kinded join semilattices

--
instance PartialOrd a => PartialOrd (Identity a) where
    Identity a1 +> Identity a2 = a1 +> a2

instance Semilattice a => Semilattice (Identity a) where
    Identity a1 \/ Identity a2 = Identity $ a1 \/ a2
    Identity a1 /\ Identity a2 = Identity $ a1 /\ a2

-- instance Bounded a => Bounded (Identity a) where -- in Data.Functor.Identity

--
instance PartialOrd a => PartialOrd (Maybe a) where
    Nothing +> Nothing = True
    Nothing +> _ = False
    _ +> Nothing = True
    Just a +> Just b = a +> b

instance Semilattice a => Semilattice (Maybe a) where
    Nothing \/ ma = ma
    ma \/ Nothing = ma
    Just a \/ Just b = Just (a \/ b)
    Nothing /\ ma = Nothing
    ma /\ Nothing = Nothing
    Just a /\ Just b = Just (a /\ b)

instance (Bounded a, Semilattice a) => Bounded (Maybe a) where
    minBound = Nothing
    maxBound = Just maxBound

propagateMaybe :: (Semilattice a, Bounded a) => Maybe a -> a -- homomorphism
propagateMaybe Nothing = minBound
propagateMaybe (Just a) = a

propagateIsJust :: Semilattice a => Maybe a -> Increasing Bool -- homomorphism
propagateIsJust = Increasing . isJust

propagateIsNothing :: Semilattice a => Maybe a -> Decreasing Bool -- homomorphism
propagateIsNothing = Decreasing . isNothing

--
instance (Ord k, PartialOrd v) => PartialOrd (M.Map k v) where
    m1 +> m2 = M.isSubmapOfBy (<+) m2 m1

instance (Ord k, Semilattice v) => Semilattice (M.Map k v) where
    (\/) = M.unionWith (\/)
    (/\) = M.intersectionWith (/\)

instance (Ord k, Enum k, Bounded k, Semilattice v, Bounded v) => Bounded (M.Map k v) where
    minBound = M.empty 
    maxBound = M.fromList $ (,maxBound) <$> [minBound..] 

propagateMap :: (Ord k, Semilattice s, Bounded s, Semilattice s, Bounded s') => Homo s s' -> Homo (M.Map k s) (M.Map k s')
propagateMap h = Homo $ fmap (homo h)

propagateMapEntry :: (Ord k, Semilattice s, Bounded s) => k -> Homo (M.Map k s) s
propagateMapEntry k = Homo $ fromMaybe minBound . M.lookup k

propagateMapKeys :: (Ord k, Semilattice s, Bounded s) => Homo (M.Map k s) (Set k)
propagateMapKeys = Homo $ M.keysSet

propagateMapValues :: (Ord k, Semilattice s, Bounded s) => Homo (M.Map k s) s
propagateMapValues = Homo $ L.foldl (\/) minBound

foo' :: Num n => Mono (M.Map k (Increasing n)) (Increasing n)
foo' = Mono $ \map -> Increasing $ sum $ increasing <$> map

--
-- instance PartialOrd a => PartialOrd [a] where
--     as1 +> as2 = length as1 >= length as2 && and (zipWith (+>) as1 as2)

-- instance Semilattice a => Semilattice [a] where
--     l1 \/ l2 = foldl1 (\/) <$> transpose [l1, l2]
--     l1 /\ l2 = zipWith (/\) l1 l2

-- instance Semilattice a, Bounded a => BoundedSemilattice [a] where
--     minBound = mempty

-- propagateListLength :: Semilattice a, Bounded a => Homo [a] (Increasing Int)
-- propagateListLength = Homo $ Increasing . length

-- propagateListElement :: Semilattice a, Bounded a => Int -> Homo [a] a
-- propagateListElement i = Homo $ \l -> if i >= length l then minBound else l !! i

-- propagateListElements :: Semilattice a, Bounded a => Int -> Homo [a] a
-- propagateListElements i = Homo bjsconcat

-- 
instance (PartialOrd a, PartialOrd b) => PartialOrd (a, b) where
    (a1, b1) +> (a2, b2) = a1 +> a2 &&  b1 +> b2

instance (Semilattice a, Semilattice b) => Semilattice (a, b) where
    (a1, b1) \/ (a2, b2) = (a1 \/ a2, b1 \/ b2)
    (a1, b1) /\ (a2, b2) = (a1 /\ a2, b1 /\ b2)

propagateFst :: (Semilattice a, Semilattice b) => Homo (a, b) a
propagateFst = Homo fst

propagateSnd :: (Semilattice a, Semilattice b) => Homo (a, b) b
propagateSnd = Homo snd

-- instance (Bounded a, Bounded b) => Bounded (a, b) where -- in GHC.Enum

--
-- instance (Semilattice a, Semilattice b, Semilattice c) => Semilattice (a, b, c) where
--     (a1, b1, c1) \/ (a2, b2, c2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2)

-- instance (Semilattice a, Bounded a, Semilattice b, Bounded b, BoundedSemilattice c) => BoundedSemilattice (a, b, c) where
--     minBound = (minBound, minBound, minBound)

-- instance (Dual a b, Dual c d, Dual e f) => Dual (a, c, e) (b, d, f) where
--     jirelement (b, d, f) = (jirelement b, jirelement d, jirelement f) 

--
-- instance (Semilattice a, Semilattice b, Semilattice c, Semilattice d) => Semilattice (a, b, c, d) where
--     (a1, b1, c1, d1) \/ (a2, b2, c2, d2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2, d1 \/ d2)

-- instance (Semilattice a, Bounded a, Semilattice b, Bounded b, BoundedSemilattice c, BoundedSemilattice d) => BoundedSemilattice (a, b, c, d) where
--     minBound = (minBound, minBound, minBound, minBound)

-- instance (Dual a b, Dual c d, Dual e f, Dual g h) => Dual (a, c, e, g) (b, d, f, h) where
--     jirelement (b, d, f, h) = (jirelement b, jirelement d, jirelement f, jirelement h) 

-- and so on...

--
instance (PartialOrd a, PartialOrd b) => PartialOrd (Either a b) where
    Left a1 +> Left a2 = a1 +> a2
    Right a1 +> Right a2 = a1 +> a2
    Left _ +> Right _ = False
    Right _ +> Left _ = True

instance (Semilattice a, Semilattice b) => Semilattice (Either a b) where
    Left a1 \/ Left a2 = Left (a1 \/ a2)
    Right b1 \/ Right b2 = Right (b1 \/ b2)
    Left _ \/ r@(Right _) = r
    r@(Right _) \/ Left _ = r
    Left a1 /\ Left a2 = Left (a1 /\ a2)
    Right b1 /\ Right b2 = Right (b1 /\ b2)
    l@(Left _) /\ Right _ = l
    Right _ /\ l@(Left _) = l

instance (Bounded a, Bounded b) => Bounded (Either a b) where
    minBound = Left minBound
    maxBound = Right maxBound

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

-- | Dual
class (Semilattice s, Bounded s, Ord b) => Dual s b | s -> b where
    -- minimal (jirelement|compose, decompose)
    -- compose . decompose = id
    decompose :: s -> Set b
    compose :: Set b -> s
    compose = S.foldl' (\s b -> s \/ jirelement b) minBound 
    -- join-irreducible element
    jirelement :: b -> s
    jirelement = compose . S.singleton

dmapToLattice :: (Dual a a', Dual b b') => Homo (Set a') (Set b') -> Homo a b
dmapToLattice (Homo f) = Homo $ \a -> compose $ f $ decompose a 

dmapToSets :: (Dual a a', Dual b b') => Homo a b -> Homo (Set a') (Set b')
dmapToSets (Homo f) = Homo $ \a's -> decompose $ f $ compose a's 

instance Dual () () where
    jirelement () = ()
    decompose () = S.singleton ()

instance Dual (Proxy a) () where
    jirelement () = Proxy
    decompose Proxy = S.singleton ()

instance Dual a b => Dual (Identity a) b where
    jirelement = Identity . jirelement
    decompose (Identity a) = decompose a

instance (Ord a, Bounded a) => Dual (Decreasing a) a where
    jirelement = Decreasing
    decompose = S.singleton . decreasing

instance (Ord a, Bounded a) => Dual (Increasing a) a where
    jirelement = Increasing
    decompose = S.singleton . increasing

instance (Enum a, Bounded a, Ord a) => Dual (Same a) a where
    jirelement = Unambiguous
    decompose Unknown = mempty
    decompose (Unambiguous a) = S.singleton a
    decompose (Ambiguous as) = as

instance (Ord a, Enum a, Bounded a) => Dual (Set a) a where
    compose = id
    decompose = id

-- higher-kinded duals
instance (Dual a b, Ord b, Enum b, Bounded b) => Dual (Maybe a) b where
    jirelement = Just . jirelement
    decompose (Just a) = decompose a
    decompose Nothing = minBound

instance (Dual a b, Dual c d) => Dual (Either a c) (Either b d) where
    jirelement (Left b) = Left $ jirelement b
    jirelement (Right d) = Right $ jirelement d
    decompose (Left a) = S.fromList (Left <$> S.toList (decompose a))
    decompose (Right c) = S.fromList (Right <$> S.toList (decompose c))

instance (Dual a b, Dual c d) => Dual (a, c) (Either b d) where
    jirelement (Left b) = (jirelement b, minBound) 
    jirelement (Right d) = (minBound, jirelement d) 
    decompose (a, c) = S.fromList (Left <$> S.toList (decompose a)) `S.union` S.fromList (Right <$> S.toList (decompose c))

-- instance Dual a b => Dual [a] (Int, b) where
--     jirelement (n, b) = replicate n minBound <> [jirelement b]
--     decompose l = S.fromList (zip [0..] l >>= (\(i, e) -> (i,) <$> S.toList (decompose e)))

instance (Ord k, Enum k, Bounded k, Dual v b) => Dual (M.Map k v) (k, b) where
    jirelement (k, b) = M.singleton k $ jirelement b
    decompose m = S.fromList (M.toList m >>= (\(k, v) -> (k,) <$> S.toList (decompose v)))

