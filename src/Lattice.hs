module Lattice (
    PartialOrd(..),
    isAscending,
    isDescending,
    Lattice(..),
    joinAll,
    meetAll,
    joinScan,
    meetScan,
    checkAscending,
    checkDescending,
    checkAscendingTo,
    checkDescendingTo,
    checkEventualConsistency,
    Distributive(..),
    Homo(..),
    joinScanHomo,
    meetScanHomo,
    Proc(..),
    joinScanProc,
    meetScanProc,
    -- | Primitive joinAll semilattices 
    Increasing(..),
    propagateIncrease,
    propagateIncrease2,
    Decreasing(..),
    propagateDecrease,
    Same(..),
    propagateSame,
    -- | Higher-kinded joinAll semilattices
    propagateMap,
    propagateMapEntry,
    propagateMapKeys,
    propagateMapValues,
    --
    propagateFst,
    propagateSnd,
    --
    Dual(..),
    dmapToLattice,
    dmapToSets,
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
import Data.Foldable as F

-- | Discrete order
type DiscreteOrd = Eq

-- | Total order
type TotalOrd = Ord

-- | Partial order
class PartialOrd p where
    {-# MINIMAL (+>) #-}
    -- a +> a - reflexivity
    -- a +> b and b +> a => a == b - antisymmetry
    -- a +> b +> c => a +> c - transitivity
    (+>) :: p -> p -> Bool -- minimal definition
    (<+) :: p -> p -> Bool
    (<+) = flip (+>)
    (<+>) :: p -> p -> Bool -- are two ps comparable
    a <+> b = a +> b || b +> a
    (>+<) :: p -> p -> Bool -- are two ps not comparable
    a >+< b = not $ a <+> b

isAscending :: (Foldable f, PartialOrd s) => f s -> Bool
isAscending = isAscending' . F.toList
    where
        isAscending' :: PartialOrd s => [s] -> Bool
        isAscending' (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest
        isAscending' _ = True

isDescending :: (Foldable f, PartialOrd s) => f s -> Bool
isDescending = isDescending' . F.toList
    where
        isDescending' :: PartialOrd s => [s] -> Bool
        isDescending' (s1:rest@(s2:_)) = s1 +> s2 && isDescending rest
        isDescending' _ = True

-- monotonic function
newtype Mono a b = Mono { mono :: a -> b }

instance Category Mono where
    id = Mono id
    h1 . h2 = Mono $ mono h1 . mono h2 

-- joinScanHomo :: (Lattice b, Bounded b) => Homo a b -> [a] -> [b]
-- joinScanHomo h = scanl (\b a -> b \/ homo h a) minBound

-- meetScanHomo :: (Lattice b, Bounded b) => Homo a b -> [a] -> [b]
-- meetScanHomo h = scanl (\b a -> b /\ homo h a) maxBound


-- | Lattice
class PartialOrd s => Lattice s where
    -- a \/ (b  \/ c) = (a \/ b) \/ c - associativity
    -- a \/ b = b \/ a - commutativity
    -- a \/ a = a idempotence
    -- a <+ a \/ b +> b - ascending
    (\/) :: s -> s -> s
    -- a /\ (b  /\ c) = (a /\ b) /\ c - associativity
    -- a /\ b = b /\ a - commutativity
    -- a /\ a = a idempotence
    -- a +> a /\ b <+ b - descending
    (/\) :: s -> s -> s

data Inverse s where
    Inverse :: s -> Inverse s

instance PartialOrd s => PartialOrd (Inverse s) where
    Inverse s1 +> Inverse s2 = s1 <+ s2

instance Lattice s => Lattice (Inverse s) where
    Inverse s1 \/ Inverse s2 = Inverse $ s1 /\ s2
    Inverse s1 /\ Inverse s2 = Inverse $ s1 \/ s2

instance Bounded s => Bounded (Inverse s) where
    minBound = maxBound
    maxBound = minBound

instance BoundedLattice s => BoundedLattice (Inverse s) where


-- | Bounded lattice
class (Lattice s, Bounded s) => BoundedLattice s where
    -- a \/ minBound = a = minBound \/ a 
    -- a /\ maxBound = a = maxBound /\ a 

joinAll :: (Foldable f, BoundedLattice s) => f s -> s
joinAll = Prelude.foldr (\/) minBound
-- if f s is bounded semilattice then it's a propagator

meetAll :: (Foldable f, BoundedLattice s) => f s -> s
meetAll = Prelude.foldr (/\) maxBound
-- if f s is bounded semilattice then it's a propagator

joinScan :: (BoundedLattice s) => [s] -> [s]
joinScan = scanl' (\/) minBound

meetScan :: (BoundedLattice s) => [s] -> [s]
meetScan = scanl' (/\) maxBound

-- physical ordering to systemic orderings
joinChains :: BoundedLattice a => [a] -> [[a]]
joinChains = fmap joinScan . L.permutations

meetChains :: BoundedLattice a => [a] -> [[a]]
meetChains = fmap meetScan . L.permutations

-- these checks Lattice laws
checkAscending :: (BoundedLattice s) => [s] -> Bool
checkAscending = isAscending . joinScan

checkDescending :: (BoundedLattice s) => [s] -> Bool
checkDescending = isDescending . meetScan

checkAscendingTo :: (BoundedLattice s, DiscreteOrd s) => [s] -> s -> Bool
checkAscendingTo [] final = final == minBound
checkAscendingTo ss final = let ss' = joinScan ss in isAscending ss' && last ss' == final

checkDescendingTo :: (BoundedLattice s, DiscreteOrd s) => [s] -> s -> Bool
checkDescendingTo [] final = final == maxBound
checkDescendingTo ss final = let ss' = meetScan ss in isDescending ss' && last ss' == final

checkEventualConsistency :: (BoundedLattice s, DiscreteOrd s) => [[s]] -> s -> Bool
checkEventualConsistency [] final = final == minBound
checkEventualConsistency ss final = checkAscendingTo (joinAll <$> ss) final

--
data Chain p where 
    Chain :: TotalOrd p => p -> Chain p

instance PartialOrd (Chain a) where
    Chain p1 +> Chain p2 = p1 >= p2

instance Lattice (Chain a) where
    Chain a1 /\ Chain a2 = Chain $ min a1 a2
    Chain a1 \/ Chain a2 = Chain $ max a1 a2

instance (TotalOrd p, Bounded p) => Bounded (Chain p) where
    minBound = Chain minBound
    maxBound = Chain maxBound

instance (Ord a, Bounded a) => BoundedLattice (Chain a)

--
data Antichain p where
    Antichain :: DiscreteOrd p => p -> Antichain p

instance DiscreteOrd p => PartialOrd (Antichain p) where
    Antichain p1 +> Antichain p2 = p1 == p2

--
newtype Homo a b = Homo { homo :: a -> b }

instance Category Homo where
    id = Homo id
    h1 . h2 = Homo $ homo h1 . homo h2 

joinScanHomo :: BoundedLattice b => Homo a b -> [a] -> [b]
joinScanHomo h = scanl (\b a -> b \/ homo h a) minBound

meetScanHomo :: BoundedLattice b => Homo a b -> [a] -> [b]
meetScanHomo h = scanl (\b a -> b /\ homo h a) maxBound

--
instance PartialOrd () where
    () +> () = True

instance Lattice () where
    _ \/ _ = ()
    _ /\ _ = ()

instance BoundedLattice ()

--
instance PartialOrd (Proxy a) where
    Proxy +> Proxy = True

instance Lattice (Proxy a) where
    _ \/ _ = Proxy
    _ /\ _ = Proxy

instance BoundedLattice (Proxy a)

--
newtype Increasing a = Increasing { increasing :: a }

deriving instance Show a => Show (Increasing a)
deriving instance Eq a => Eq (Increasing a)

instance Ord a => PartialOrd (Increasing a) where
    (Increasing a) +> (Increasing b) = a >= b
    
instance Ord a => Lattice (Increasing a) where
    (Increasing a) \/ (Increasing b) = Increasing (max a b)
    (Increasing a) /\ (Increasing b) = Increasing (min a b)

instance (Ord a, Bounded a) => Bounded (Increasing a) where
    minBound = Increasing minBound
    maxBound = Increasing maxBound

instance (Ord a, Bounded a) => BoundedLattice (Increasing a) 


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

instance Ord a => Lattice (Decreasing a) where
    (Decreasing a) \/ (Decreasing b) = Decreasing (min a b)
    (Decreasing a) /\ (Decreasing b) = Decreasing (max a b)

instance (Ord a, Bounded a) => Bounded (Decreasing a) where
    minBound = Decreasing minBound
    maxBound = Decreasing maxBound

instance (Ord a, Bounded a) => BoundedLattice (Decreasing a) 

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

instance Ord a => Lattice (Set a) where
    (\/) = S.union
    (/\) = S.intersection

instance (Ord a, Enum a, Bounded a) => Bounded (Set a) where
    minBound = mempty
    maxBound = fromList [minBound..]

instance (Ord a, Enum a, Bounded a) => BoundedLattice (Set a) 


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

instance Ord a => Lattice (Same a) where
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

instance (Enum a, Ord a, Bounded a) => BoundedLattice (Same a) 


propagateSame :: (Ord a, Ord b) => (a -> b) -> Same a -> Same b
propagateSame f Unknown = Unknown
propagateSame f (Unambiguous a) = Unambiguous (f a)
propagateSame f (Ambiguous as) = Ambiguous (S.map f as)

-- higher kinded join semilattices

--
instance PartialOrd a => PartialOrd (Identity a) where
    Identity a1 +> Identity a2 = a1 +> a2

instance Lattice a => Lattice (Identity a) where
    Identity a1 \/ Identity a2 = Identity $ a1 \/ a2
    Identity a1 /\ Identity a2 = Identity $ a1 /\ a2

instance BoundedLattice a => BoundedLattice (Identity a)

--
instance PartialOrd a => PartialOrd (Maybe a) where
    Nothing +> Nothing = True
    Nothing +> _ = False
    _ +> Nothing = True
    Just a +> Just b = a +> b

instance Lattice a => Lattice (Maybe a) where
    Nothing \/ ma = ma
    ma \/ Nothing = ma
    Just a \/ Just b = Just (a \/ b)
    Nothing /\ ma = Nothing
    ma /\ Nothing = Nothing
    Just a /\ Just b = Just (a /\ b)

instance (Bounded a, Lattice a) => Bounded (Maybe a) where
    minBound = Nothing
    maxBound = Just maxBound

instance BoundedLattice a => BoundedLattice (Maybe a)

propagateMaybe :: (Lattice a, Bounded a) => Maybe a -> a -- homomorphism
propagateMaybe Nothing = minBound
propagateMaybe (Just a) = a

propagateIsJust :: Lattice a => Maybe a -> Increasing Bool -- homomorphism
propagateIsJust = Increasing . isJust

propagateIsNothing :: Lattice a => Maybe a -> Decreasing Bool -- homomorphism
propagateIsNothing = Decreasing . isNothing

--
instance (Ord k, PartialOrd v) => PartialOrd (M.Map k v) where
    m1 +> m2 = M.isSubmapOfBy (<+) m2 m1

instance (Ord k, Lattice v) => Lattice (M.Map k v) where
    (\/) = M.unionWith (\/)
    (/\) = M.intersectionWith (/\)

instance (Ord k, Enum k, Bounded k, Lattice v, Bounded v) => Bounded (M.Map k v) where
    minBound = M.empty 
    maxBound = M.fromList $ (,maxBound) <$> [minBound..] 

instance (Ord k, Enum k, Bounded k, BoundedLattice v) => BoundedLattice (M.Map k v)


propagateMap :: (Ord k, BoundedLattice s, BoundedLattice s') => Homo s s' -> Homo (M.Map k s) (M.Map k s')
propagateMap h = Homo $ fmap (homo h)

propagateMapEntry :: (Ord k, BoundedLattice s) => k -> Homo (M.Map k s) s
propagateMapEntry k = Homo $ fromMaybe minBound . M.lookup k

propagateMapKeys :: (Ord k, BoundedLattice s) => Homo (M.Map k s) (Set k)
propagateMapKeys = Homo M.keysSet

propagateMapValues :: (Ord k, BoundedLattice s) => Homo (M.Map k s) s
propagateMapValues = Homo $ L.foldl (\/) minBound

foo' :: Num n => M.Map k (Increasing n) -> Increasing n
foo' map = Increasing $ sum $ increasing <$> map

-- 
instance (PartialOrd a, PartialOrd b) => PartialOrd (a, b) where
    (a1, b1) +> (a2, b2) = a1 +> a2 &&  b1 +> b2

instance (Lattice a, Lattice b) => Lattice (a, b) where
    (a1, b1) \/ (a2, b2) = (a1 \/ a2, b1 \/ b2)
    (a1, b1) /\ (a2, b2) = (a1 /\ a2, b1 /\ b2)

-- instance (Bounded a, Bounded b) => Bounded (a, b) where -- in GHC.Enum

instance (BoundedLattice a, BoundedLattice b) => BoundedLattice (a, b)

propagateFst :: (Lattice a, Lattice b) => Homo (a, b) a
propagateFst = Homo fst

propagateSnd :: (Lattice a, Lattice b) => Homo (a, b) b
propagateSnd = Homo snd

--
instance (PartialOrd a, PartialOrd b) => PartialOrd (Either a b) where
    Left a1 +> Left a2 = a1 +> a2
    Right a1 +> Right a2 = a1 +> a2
    Left _ +> Right _ = False
    Right _ +> Left _ = True

instance (Lattice a, Lattice b) => Lattice (Either a b) where
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


instance (BoundedLattice a, BoundedLattice b) => BoundedLattice (Either a b)

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

-- 
class Lattice s => Distributive s
    -- a /\ (b \/ c) = (a /\ b) \/ (a \/ c)

instance Distributive ()
instance Distributive (Proxy a)
instance Ord a => Distributive (Set a)
instance Ord a => Distributive (Increasing a)
instance Ord a => Distributive (Decreasing a)
instance Ord a => Distributive (Same a)
instance Distributive a => Distributive (Identity a)
instance Distributive a => Distributive (Maybe a)
instance (Ord k, Distributive v) => Distributive (M.Map k v)
instance (Distributive a, Distributive b) => Distributive (a, b)
instance (Distributive a, Distributive b) => Distributive (Either a b)

-- | Dual
class (Distributive s, BoundedLattice s) => Dual s s' | s -> s' where
    -- join-irreducible element
    jirelement :: s' -> s

accumulate :: Dual s s' => Homo (Set s') s -- it's a homomorphism indeed
accumulate = Homo $ \set -> S.foldl' (\s s' -> s \/ jirelement s') minBound set

bar :: Lattice a => Homo (Set s') a -> s' -> a -> a
bar h s' a = homo h (S.singleton s') \/ a

dmapToLattice :: (Dual a a', Dual b b') => Homo (Set a') (Set b') -> Homo a b
dmapToLattice h = undefined 
-- dmapToLattice h = compose . h . reduce

dmapToSets :: (Dual a a', Dual b b') => Homo a b -> Homo (Set a') (Set b')
dmapToSets h = undefined
-- dmapToSets h = reduce . h . compose

-- physical ordering to systemic orderings
joinCompositions :: Dual a a' => [a'] -> [[a]]
joinCompositions = fmap joinScan . L.permutations . fmap jirelement

meetCompositions :: Dual a a' => [a'] -> [[a]]
meetCompositions = fmap meetScan . L.permutations . fmap jirelement


instance Dual () () where
    jirelement = id

instance Dual (Proxy a) () where
    jirelement () = Proxy

instance (Ord a, BoundedLattice a) => Dual (Decreasing a) a where
    jirelement = Decreasing

instance (Ord a, BoundedLattice a) => Dual (Increasing a) a where
    jirelement = Increasing

instance (Enum a, BoundedLattice a, Ord a) => Dual (Same a) a where
    jirelement = Unambiguous

instance (Ord a, Enum a, Bounded a) => Dual (Set a) a where
    jirelement = S.singleton

-- higher-kinded duals
instance Dual a b => Dual (Identity a) b where
    jirelement = Identity . jirelement

instance Dual a b => Dual (Maybe a) (Maybe b) where -- ?
    jirelement = jirelement'
        where
            jirelement' Nothing = Nothing
            jirelement' (Just b) = Just $ jirelement b

instance (Dual a b, Dual c d) => Dual (Either a c) (Either b d) where
    jirelement = jirelement'
        where
            jirelement' (Left b) = Left $ jirelement b
            jirelement' (Right d) = Right $ jirelement d

instance (Dual a b, Dual c d) => Dual (a, c) (Either b d) where
    jirelement = jirelement'
        where
            jirelement' (Left b) = (jirelement b, minBound) 
            jirelement' (Right d) = (minBound, jirelement d)

instance (Ord k, Enum k, Bounded k, Dual v b) => Dual (M.Map k v) (k, b) where
    jirelement = jirelement'
        where
            jirelement' (k, b) = M.singleton k $ jirelement b

--
data Proc a b = forall s. (BoundedLattice s) => Proc { phomo :: Homo a s, pf :: s -> b }

joinScanProc :: Proc a b -> [a] -> [b]
joinScanProc (Proc h m) = fmap m . joinScanHomo h

meetScanProc :: Proc a b -> [a] -> [b]
meetScanProc (Proc h m) = fmap m . meetScanHomo h

instance Functor (Proc a) where
    fmap f (Proc h g) = Proc h (f . g)

instance Applicative (Proc a) where
    pure b = Proc foo (const b)
        where
            foo :: Homo a ()
            foo = Homo (const ())
    (Proc fh fm) <*> (Proc ah am) = Proc (Homo $ \i -> (homo fh i, homo ah i)) (\(fs, as) -> fm fs (am as))

procid :: BoundedLattice a => Proc a a
procid = Proc id id

procbimap :: Homo a' a -> (b -> b') -> Proc a b -> Proc a' b'
procbimap h m (Proc ph pm) = Proc (ph . h) (m . pm)
