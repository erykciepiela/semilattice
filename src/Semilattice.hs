module Semilattice (
    Semilattice(..),
    BoundedSemilattice(..),
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
    GrowingList(..),
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

class Semilattice s => BoundedSemilattice s where
    -- a \/ bottom = a = bottom \/ a 
    bottom :: s
    -- a /\ top = top = top /\ a 
    -- top :: s

bjsconcatS :: (Ord s, BoundedSemilattice s) => S.Set s -> s
bjsconcatS = S.foldr (\/) bottom

bjsconcat :: (Foldable f, BoundedSemilattice s) => f s -> s
bjsconcat = Prelude.foldr (\/) bottom
-- if f s is bounded semilattice then it's a propagator

bjsscan :: (BoundedSemilattice s) => [s] -> [s]
bjsscan = scanl' (\/) bottom

bjsconcat'' :: (Foldable f, BoundedSemilattice s, BoundedSemilattice (f s)) => f s -> s
bjsconcat'' = Prelude.foldr (\/) bottom


ascends :: (Eq s, BoundedSemilattice s) => [s] -> Bool
ascends ss = let ss' = bjsscan ss in isAscending ss'
    where
        isAscending :: (Eq s, BoundedSemilattice s) => [s] -> Bool
        isAscending [] = True
        isAscending [s] = True
        isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest

ascendsTowards :: (Eq s, BoundedSemilattice s) => [s] -> s -> Bool
ascendsTowards [] final = final == bottom
ascendsTowards ss final = let ss' = bjsscan ss in isAscending ss' && L.all (<+ final) ss'

isAscending :: (Eq s, PartialOrd s) => [s] -> Bool
isAscending [] = True
isAscending [s] = True
isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest

isAscendingTowards :: (Eq s, PartialOrd s) => [s] -> s -> Bool
isAscendingTowards ss s = isAscending ss && last ss == s -- assuming ss not empty

ascendsTo :: (Eq s, BoundedSemilattice s) => [s] -> s -> Bool
ascendsTo [] final = final == bottom
ascendsTo ss final = let ss' = bjsscan ss in isAscending ss' && L.all (<+ final) ss' && last ss' == final
-- ascendsTo ss final = let ss' = bjsscan ss in last ss' == final
    where
        isAscending :: (Eq s, BoundedSemilattice s) => [s] -> Bool
        isAscending [] = True
        isAscending [s] = True
        isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest

isEventuallyConsistent :: (Eq s, BoundedSemilattice s) => [[s]] -> s -> Bool
isEventuallyConsistent [] final = final == bottom
isEventuallyConsistent ss final = ascendsTo (bjsconcat <$> ss) final

isDescending :: (Eq s, BoundedSemilattice s) => [s] -> Bool
isDescending [] = True
isDescending [s] = True
isDescending (s1:rest@(s2:_)) = s1 +> s2 && isDescending rest

--
class (BoundedSemilattice s, Ord b) => Dual s b | s -> b where
    -- minimal (jirelement|compose, decompose)
    -- compose . decompose = id
    decompose :: s -> Set b
    compose :: Set b -> s
    compose = S.foldl' (\s b -> s \/ jirelement b) bottom 
    -- join-irreducible element
    jirelement :: b -> s
    jirelement = compose . S.singleton

dmapToLattice :: (Dual a a', Dual b b') => Homo (Set a') (Set b') -> Homo a b
dmapToLattice (Homo f) = Homo $ \a -> compose $ f $ decompose a 

dmapToSets :: (Dual a a', Dual b b') => Homo a b -> Homo (Set a') (Set b')
dmapToSets (Homo f) = Homo $ \a's -> decompose $ f $ compose a's 

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
collect = scanl (\s a -> s \/ jirelement a) bottom

propagateHomo :: (BoundedSemilattice a, BoundedSemilattice b) => Homo a b -> [a] -> [b]
propagateHomo (Homo f) = scanl (\b a -> b \/ f a) bottom

propagatedHomo :: (BoundedSemilattice a, BoundedSemilattice b) => [a] -> Homo a b -> [b]
propagatedHomo = flip propagateHomo

-- propagatedHomo' :: (BoundedSemilattice a, BoundedSemilattice b) => [[a]] -> Homo a b -> [b]
-- propagatedHomo' ass (Homo f) = scanl (\b a -> b \/ f a) bottom
--
newtype Mono a b = Mono { mono :: a -> b }

instance Category Mono where
    id = Mono id
    m1 . m2 = Mono $ mono m1 . mono m2 

propagateMono :: (BoundedSemilattice a, PartialOrd b) => Mono a b -> [a] -> [b]
propagateMono (Mono f) as = f <$> scanl (\/) bottom as 

propagatedMono :: (BoundedSemilattice a, PartialOrd b) => [a] -> Mono a b -> [b]
propagatedMono = flip propagateMono

data Proc a b = forall s. BoundedSemilattice s => Proc { phomo :: Homo a s, pf :: s -> b }

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

procid :: BoundedSemilattice a => Proc a a
procid = Proc id id

procbimap :: Homo a' a -> (b -> b') -> Proc a b -> Proc a' b'
procbimap h m (Proc ph pm) = Proc (ph . h) (m . pm)

--
instance PartialOrd () where
    () +> () = True

instance Semilattice () where
    _ \/ _ = ()
    _ /\ _ = ()

instance BoundedSemilattice () where
    bottom = mempty

instance Dual () () where
    jirelement () = ()
    decompose () = S.singleton ()

--
instance PartialOrd (Proxy a) where
    Proxy +> Proxy = True

instance Semilattice (Proxy a) where
    _ \/ _ = Proxy
    _ /\ _ = Proxy

instance BoundedSemilattice (Proxy a) where
    bottom = mempty

instance Dual (Proxy a) () where
    jirelement () = Proxy
    decompose Proxy = S.singleton ()

--
newtype Increasing a = Increasing { increasing :: a }

deriving instance Show a => Show (Increasing a)
deriving instance Eq a => Eq (Increasing a)

instance Ord a => PartialOrd (Increasing a) where
    (Increasing a) +> (Increasing b) = a >= b
    
instance Ord a => Semilattice (Increasing a) where
    (Increasing a) \/ (Increasing b) = Increasing (max a b)
    (Increasing a) /\ (Increasing b) = Increasing (min a b)

instance (Ord a, Bounded a) => BoundedSemilattice (Increasing a) where
    bottom = Increasing minBound

instance (Ord a, Bounded a) => Dual (Increasing a) a where
    jirelement = Increasing
    decompose = S.singleton . increasing

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

instance (Ord a, Bounded a) => BoundedSemilattice (Decreasing a) where
    bottom = Decreasing maxBound

instance (Ord a, Bounded a) => Dual (Decreasing a) a where
    jirelement = Decreasing
    decompose = S.singleton . decreasing

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

instance Ord a => BoundedSemilattice (Set a) where
    bottom = mempty

instance Ord a => Dual (Set a) a where
    compose = id
    decompose = id

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

instance Ord a => BoundedSemilattice (Same a) where
    bottom = Unknown

instance Ord a => Dual (Same a) a where
    jirelement = Unambiguous
    decompose Unknown = mempty
    decompose (Unambiguous a) = S.singleton a
    decompose (Ambiguous as) = as


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

instance BoundedSemilattice a => BoundedSemilattice (Identity a) where
    bottom = Identity bottom

instance Dual a b => Dual (Identity a) b where
    jirelement = Identity . jirelement
    decompose (Identity a) = decompose a

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

instance Semilattice a => BoundedSemilattice (Maybe a) where
    bottom = Nothing

instance Dual a b => Dual (Maybe a) b where
    jirelement = Just . jirelement
    decompose (Just a) = decompose a

propagateMaybe :: BoundedSemilattice a => Maybe a -> a -- homomorphism
propagateMaybe Nothing = bottom
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

instance (Ord k, BoundedSemilattice v) => BoundedSemilattice (M.Map k v) where
    bottom = mempty

instance (Ord k, Dual v b) => Dual (M.Map k v) (k, b) where
    jirelement (k, b) = M.singleton k $ jirelement b
    decompose m = S.fromList (M.toList m >>= (\(k, v) -> (k,) <$> S.toList (decompose v)))

propagateMap :: (Ord k, BoundedSemilattice s, BoundedSemilattice s') => Homo s s' -> Homo (M.Map k s) (M.Map k s')
propagateMap h = Homo $ fmap (homo h)

propagateMapEntry :: (Ord k, BoundedSemilattice s) => k -> Homo (M.Map k s) s
propagateMapEntry k = Homo $ fromMaybe bottom . M.lookup k

propagateMapKeys :: (Ord k, BoundedSemilattice s) => Homo (M.Map k s) (Set k)
propagateMapKeys = Homo $ M.keysSet

propagateMapValues :: (Ord k, BoundedSemilattice s) => Homo (M.Map k s) s
propagateMapValues = Homo $ L.foldl (\/) bottom

foo' :: Num n => Mono (M.Map k (Increasing n)) (Increasing n)
foo' = Mono $ \map -> Increasing $ sum $ increasing <$> map

--
newtype GrowingList a = GrowingList { growingList :: [a] }

deriving instance Eq a => Eq (GrowingList a)

instance PartialOrd a => PartialOrd (GrowingList a) where
    GrowingList as1 +> GrowingList as2 = length as1 >= length as2 && and (zipWith (+>) as1 as2)

instance Semilattice a => Semilattice (GrowingList a) where
    GrowingList l1 \/ GrowingList l2 = GrowingList $ foldl1 (\/) <$> transpose [l1, l2]
    GrowingList l1 /\ GrowingList l2 = GrowingList $ zipWith (/\) l1 l2

instance BoundedSemilattice a => BoundedSemilattice (GrowingList a) where
    bottom = GrowingList []

instance Dual a b => Dual (GrowingList a) (Int, b) where
    jirelement (n, b) = GrowingList $ replicate n bottom <> [jirelement b]
    decompose (GrowingList l) = S.fromList (zip [0..] l >>= (\(i, e) -> (i,) <$> S.toList (decompose e)))

propagateListLength :: BoundedSemilattice a => Homo (GrowingList a) (Increasing Int)
propagateListLength = Homo $ \(GrowingList l) -> Increasing (length l)

propagateListElement :: BoundedSemilattice a => Int -> Homo (GrowingList a) a
propagateListElement i = Homo $ \(GrowingList l) -> if i >= length l then bottom else l !! i

propagateListElements :: BoundedSemilattice a => Int -> Homo (GrowingList a) a
propagateListElements i = Homo $ \(GrowingList l) -> bjsconcat l

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

instance (BoundedSemilattice a, BoundedSemilattice b) => BoundedSemilattice (a, b) where
    bottom = (bottom, bottom)

instance (Dual a b, Dual c d) => Dual (a, c) (Either b d) where
    jirelement (Left b) = (jirelement b, bottom) 
    jirelement (Right d) = (bottom, jirelement d) 
    decompose (a, c) = S.fromList (Left <$> S.toList (decompose a)) `S.union` S.fromList (Right <$> S.toList (decompose c))

--
-- instance (Semilattice a, Semilattice b, Semilattice c) => Semilattice (a, b, c) where
--     (a1, b1, c1) \/ (a2, b2, c2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2)

-- instance (BoundedSemilattice a, BoundedSemilattice b, BoundedSemilattice c) => BoundedSemilattice (a, b, c) where
--     bottom = (bottom, bottom, bottom)

-- instance (Dual a b, Dual c d, Dual e f) => Dual (a, c, e) (b, d, f) where
--     jirelement (b, d, f) = (jirelement b, jirelement d, jirelement f) 

--
-- instance (Semilattice a, Semilattice b, Semilattice c, Semilattice d) => Semilattice (a, b, c, d) where
--     (a1, b1, c1, d1) \/ (a2, b2, c2, d2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2, d1 \/ d2)

-- instance (BoundedSemilattice a, BoundedSemilattice b, BoundedSemilattice c, BoundedSemilattice d) => BoundedSemilattice (a, b, c, d) where
--     bottom = (bottom, bottom, bottom, bottom)

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

instance (BoundedSemilattice a, Semilattice b) => BoundedSemilattice (Either a b) where
    bottom = Left bottom

instance (Dual a b, Dual c d) => Dual (Either a c) (Either b d) where
    jirelement (Left b) = Left $ jirelement b
    jirelement (Right d) = Right $ jirelement d
    decompose (Left a) = S.fromList (Left <$> S.toList (decompose a))
    decompose (Right c) = S.fromList (Right <$> S.toList (decompose c))

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

-- data E s where
--     E :: (Ord s, BoundedSemilattice s) => GrowingSet s -> E s

-- pHomo :: (BoundedSemilattice a) => (a -> b) -> GrowingSet a -> b
-- pHomo f g = f $ join g

-- pMono :: (BoundedSemilattice a, BoundedSemilattice b, Ord b) => (a -> b) -> GrowingSet a -> b
-- pMono f g = bjsconcat $ S.map f (Semilattice.all g)

-- join :: (BoundedSemilattice s) => GrowingSet s -> s
-- join (GrowingSet ss) = bjsconcat ss

-- all :: (BoundedSemilattice s) => GrowingSet s -> S.Set s
-- all (GrowingSet ss) = ss
