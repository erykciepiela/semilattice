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

type DiscreteOrd = Eq -- antichain

type TotalOrd = Ord -- chain

-- | Partial order
-- | (Eq is discrete order)
class DiscreteOrd p => PartialOrd p where
    -- a == b => a +> b and b +> a -- reflexivity
    -- a +> b and b +> a => a == b - antisymmetry
    -- a +> b +> c => a +> c - transitivity
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

isAscending :: PartialOrd s => [s] -> Bool
isAscending (s1:rest@(s2:_)) = s1 <+ s2 && isAscending rest
isAscending _ = True

isDescending :: PartialOrd s => [s] -> Bool
isDescending (s1:rest@(s2:_)) = s1 +> s2 && isDescending rest
isDescending _ = True

-- monotonic function
newtype Mono a b = Mono { mono :: a -> b }

instance Category Mono where
    id = Mono id
    h1 . h2 = Mono $ mono h1 . mono h2 

-- joinScanHomo :: (Lattice b, Bounded b) => Homo a b -> [a] -> [b]
-- joinScanHomo h = scanl (\b a -> b \/ homo h a) minBound

-- meetScanHomo :: (Lattice b, Bounded b) => Homo a b -> [a] -> [b]
-- meetScanHomo h = scanl (\b a -> b /\ homo h a) maxBound


--
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
    -- if s is also Bounded then
    -- a \/ minBound = a = minBound \/ a 
    -- a /\ maxBound = a = maxBound /\ a 

joinAll :: (Foldable f, Lattice s, Bounded s) => f s -> s
joinAll = Prelude.foldr (\/) minBound
-- if f s is bounded semilattice then it's a propagator

meetAll :: (Foldable f, Lattice s, Bounded s) => f s -> s
meetAll = Prelude.foldr (/\) maxBound
-- if f s is bounded semilattice then it's a propagator

joinScan :: (Lattice s, Bounded s) => [s] -> [s]
joinScan = scanl' (\/) minBound

meetScan :: (Lattice s, Bounded s) => [s] -> [s]
meetScan = scanl' (/\) maxBound

-- physical ordering to systemic orderings
joinChains :: (Lattice a, Bounded a) => [a] -> [[a]]
joinChains = fmap joinScan . L.permutations

meetChains :: (Lattice a, Bounded a) => [a] -> [[a]]
meetChains = fmap meetScan . L.permutations

-- these checks Lattice laws
checkAscending :: (Lattice s, Bounded s) => [s] -> Bool
checkAscending = isAscending . joinScan

checkDescending :: (Lattice s, Bounded s) => [s] -> Bool
checkDescending = isDescending . meetScan

checkAscendingTo :: (Lattice s, Bounded s) => [s] -> s -> Bool
checkAscendingTo [] final = final == minBound
checkAscendingTo ss final = let ss' = joinScan ss in isAscending ss' && last ss' == final

checkDescendingTo :: (Lattice s, Bounded s) => [s] -> s -> Bool
checkDescendingTo [] final = final == maxBound
checkDescendingTo ss final = let ss' = meetScan ss in isDescending ss' && last ss' == final

checkEventualConsistency :: (Lattice s, Bounded s) => [[s]] -> s -> Bool
checkEventualConsistency [] final = final == minBound
checkEventualConsistency ss final = checkAscendingTo (joinAll <$> ss) final

--
newtype Homo a b = Homo { homo :: a -> b }

instance Category Homo where
    id = Homo id
    h1 . h2 = Homo $ homo h1 . homo h2 

joinScanHomo :: (Lattice b, Bounded b) => Homo a b -> [a] -> [b]
joinScanHomo h = scanl (\b a -> b \/ homo h a) minBound

meetScanHomo :: (Lattice b, Bounded b) => Homo a b -> [a] -> [b]
meetScanHomo h = scanl (\b a -> b /\ homo h a) maxBound

--
data Proc a b = forall s. (Lattice s, Bounded s) => Proc { phomo :: Homo a s, pf :: s -> b }

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

procid :: (Lattice a, Bounded a) => Proc a a
procid = Proc id id

procbimap :: Homo a' a -> (b -> b') -> Proc a b -> Proc a' b'
procbimap h m (Proc ph pm) = Proc (ph . h) (m . pm)

--
instance PartialOrd () where
    () +> () = True

instance Lattice () where
    _ \/ _ = ()
    _ /\ _ = ()

-- instance Bounded () where -- in GHC.Enum

--
instance PartialOrd (Proxy a) where
    Proxy +> Proxy = True

instance Lattice (Proxy a) where
    _ \/ _ = Proxy
    _ /\ _ = Proxy

-- instance Bounded (Proxy a) where -- in Data.Proxy

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

-- instance Bounded a => Bounded (Identity a) where -- in Data.Functor.Identity

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

propagateMap :: (Ord k, Lattice s, Bounded s, Lattice s, Bounded s') => Homo s s' -> Homo (M.Map k s) (M.Map k s')
propagateMap h = Homo $ fmap (homo h)

propagateMapEntry :: (Ord k, Lattice s, Bounded s) => k -> Homo (M.Map k s) s
propagateMapEntry k = Homo $ fromMaybe minBound . M.lookup k

propagateMapKeys :: (Ord k, Lattice s, Bounded s) => Homo (M.Map k s) (Set k)
propagateMapKeys = Homo M.keysSet

propagateMapValues :: (Ord k, Lattice s, Bounded s) => Homo (M.Map k s) s
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
class (Distributive s, Bounded s) => Dual s s' | s -> s' where
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
    -- reduce = Homo $ const $ S.empty

instance Dual (Proxy a) () where
    jirelement () = Proxy
    -- reduce = Homo $ const $ S.empty

instance (Ord a, Bounded a) => Dual (Decreasing a) a where
    jirelement = Decreasing
    -- reduce = Homo $ S.singleton . decreasing

instance (Ord a, Bounded a) => Dual (Increasing a) a where
    jirelement = Increasing
    -- reduce = Homo $ S.singleton . increasing

instance (Enum a, Bounded a, Ord a) => Dual (Same a) a where
    jirelement = Unambiguous
    -- reduce = Homo reduce'
    --     where
    --         reduce' Unknown = mempty
    --         reduce' (Unambiguous a) = S.singleton a
    --         reduce' (Ambiguous as) = as

instance (Ord a, Enum a, Bounded a) => Dual (Set a) a where
    jirelement = S.singleton
    -- reduce = id

-- higher-kinded duals
instance Dual a b => Dual (Identity a) b where
    jirelement = Identity . jirelement
    -- reduce = Homo $ \(Identity a) -> homo reduce a

instance Dual a b => Dual (Maybe a) (Maybe b) where -- ?
    jirelement = jirelement'
        where
            jirelement' Nothing = Nothing
            jirelement' (Just b) = Just $ jirelement b
    -- reduce = Homo reduce'
    --     where
    --         reduce' Nothing = S.empty
    --         reduce' (Just a) = S.fromList (Just <$> S.toList (homo reduce a)) -- ?

instance (Dual a b, Dual c d) => Dual (Either a c) (Either b d) where
    jirelement = jirelement'
        where
            jirelement' (Left b) = Left $ jirelement b
            jirelement' (Right d) = Right $ jirelement d
    -- reduce = Homo reduce'
    --     where
    --         reduce' (Left a) = S.fromList (Left <$> S.toList (homo reduce a))
    --         reduce' (Right c) = S.fromList (Right <$> S.toList (homo reduce c))

instance (Dual a b, Dual c d) => Dual (a, c) (Either b d) where
    jirelement = jirelement'
        where
            jirelement' (Left b) = (jirelement b, minBound) 
            jirelement' (Right d) = (minBound, jirelement d)
    -- reduce = Homo reduce'
    --     where
    --         reduce' (a, c) = S.fromList (Left <$> S.toList (homo reduce a)) `S.union` S.fromList (Right <$> S.toList (homo reduce c))

instance (Ord k, Enum k, Bounded k, Dual v b) => Dual (M.Map k v) (k, b) where
    jirelement = jirelement'
        where
            jirelement' (k, b) = M.singleton k $ jirelement b
    -- reduce = Homo reduce'
    --     where
    --         reduce' m = S.fromList (M.toList m >>= (\(k, v) -> (k,) <$> S.toList (homo reduce v)))
