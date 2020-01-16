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
    Proc(..),
    runProc,
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
    propagateMapKeys,
    propagateMapValues,
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

class PartialOrd s => JoinSemilattice s where
    -- a \/ (b  \/ c) = (a \/ b) \/ c - associativity
    -- a \/ b = b \/ a - commutativity
    -- a \/ a = a idempotence
    -- a \/ b +> a
    -- a \/ b +> b
    (\/) :: s -> s -> s

class PartialOrd s => MeetSemilattice s where
    -- a /\ (b  /\ c) = (a /\ b) /\ c - associativity
    -- a /\ b = b /\ a - commutativity
    -- a /\ a = a idempotence
    -- a /\ b <+ a
    -- a /\ b <+ b
    (/\) :: s -> s -> s

class (JoinSemilattice s, MeetSemilattice s) => Semilattice s

class JoinSemilattice s => BoundedJoinSemilattice s where
    -- a \/ bottom = a = bottom \/ a 
    bottom :: s

class MeetSemilattice s => BoundedMeetSemilattice s where
    -- a /\ top = top = top /\ a 
    top :: s

class (BoundedJoinSemilattice s, BoundedMeetSemilattice s) => BoundedSemilattice s

bjsconcatS :: (Ord s, BoundedJoinSemilattice s) => S.Set s -> s
bjsconcatS = S.foldr (\/) bottom

bjsconcat :: (Foldable f, BoundedJoinSemilattice s) => f s -> s
bjsconcat = Prelude.foldr (\/) bottom
-- if f s is bounded semilattice then it's a propagator

bjsscan :: (BoundedJoinSemilattice s) => [s] -> [s]
bjsscan = scanl' (\/) bottom

bjsconcat'' :: (Foldable f, BoundedJoinSemilattice s, BoundedJoinSemilattice (f s)) => f s -> s
bjsconcat'' = Prelude.foldr (\/) bottom


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
newtype Mono a b = Mono { mono :: a -> b }

instance Category Mono where
    id = Mono id
    m1 . m2 = Mono $ mono m1 . mono m2 

-- data ProcM a b = forall s. BoundedJoinSemilattice s => ProcM { pmhomo :: Homo a s, pmmono :: Mono s b }

data Proc a b = forall s. BoundedJoinSemilattice s => Proc { phomo :: Homo a s, pf :: s -> b }

runProc :: Proc a b -> [a] -> [b]
runProc (Proc (Homo h) m) as = m <$> bjsscan (h <$> as)

instance Functor (Proc a) where
    fmap f (Proc h g) = Proc h (f . g)

foo :: Homo a ()
foo = Homo (const ())

instance Applicative (Proc a) where
    pure b = Proc foo (const b)
    (Proc fh fm) <*> (Proc ah am) = Proc (Homo $ \i -> (homo fh i, homo ah i)) (\(fs, as) -> fm fs (am as))

procid :: BoundedJoinSemilattice a => Proc a a
procid = Proc id id

procbimap :: Homo a' a -> (b -> b') -> Proc a b -> Proc a' b'
procbimap h m (Proc ph pm) = Proc (ph . h) (m . pm)

--
instance PartialOrd () where
    () +> () = True

instance JoinSemilattice () where
    (\/) = (<>)

instance BoundedJoinSemilattice () where
    bottom = mempty

instance Based () () where
    jirelement = id

--
instance PartialOrd (Proxy a) where
    Proxy +> Proxy = True

instance JoinSemilattice (Proxy a) where
    (\/) = (<>)

instance BoundedJoinSemilattice (Proxy a) where
    bottom = mempty

instance Based (Proxy a) () where
    jirelement _ = Proxy

--
newtype Increasing a = Increasing { increasing :: a }

deriving instance Show a => Show (Increasing a)
deriving instance Eq a => Eq (Increasing a)

instance Num a => Num (Increasing a) where
    fromInteger = Increasing . fromInteger

instance Ord a => PartialOrd (Increasing a) where
    (Increasing a) +> (Increasing b) = a >= b
    
instance Ord a => JoinSemilattice (Increasing a) where
    (Increasing a) \/ (Increasing b) = Increasing (max a b)

instance (Ord a, Bounded a) => BoundedJoinSemilattice (Increasing a) where
    bottom = Increasing minBound

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

--
newtype Decreasing a = Decreasing { decreasing :: a }

deriving instance Show a => Show (Decreasing a)
deriving instance Eq a => Eq (Decreasing a)

instance Ord a => PartialOrd (Decreasing a) where
    Decreasing a +> Decreasing b = a <= b

instance Ord a => JoinSemilattice (Decreasing a) where
    (Decreasing a) \/ (Decreasing b) = Decreasing (min a b)

instance (Ord a, Bounded a) => BoundedJoinSemilattice (Decreasing a) where
    bottom = Decreasing maxBound

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
newtype GrowingSet a = GrowingSet { growingSet :: Set a }

deriving instance Show a => Show (GrowingSet a)
deriving instance Eq a => Eq (GrowingSet a)

instance Ord a => PartialOrd (GrowingSet a) where
    GrowingSet s1 +> GrowingSet s2 = s1 >= s2

instance Ord a => JoinSemilattice (GrowingSet a) where
    GrowingSet s1 \/ GrowingSet s2 = GrowingSet $ S.union s1 s2

instance Ord a => BoundedJoinSemilattice (GrowingSet a) where
    bottom = GrowingSet $ mempty

instance Ord a => Based (GrowingSet a) a where
    jirelement = GrowingSet . S.singleton

propagateGrowth :: (Ord a, Ord b) => (a -> b) -> GrowingSet a -> GrowingSet b
propagateGrowth f = GrowingSet . S.map f . growingSet

-- | If @a@ is Ord and we know we get fewer of them over time.
newtype ShrinkingSet a = ShrinkingSet { shrinkingSet :: Set a }

deriving instance Show a => Show (ShrinkingSet a)
deriving instance Eq a => Eq (ShrinkingSet a)

instance Ord a => PartialOrd (ShrinkingSet a) where
    ShrinkingSet s1 +> ShrinkingSet s2 = s1 <= s2

instance Ord a => JoinSemilattice (ShrinkingSet a) where
    ShrinkingSet s1 \/ ShrinkingSet s2 = ShrinkingSet $ S.intersection s1 s2

instance (Ord a, Enum a, Bounded a) => BoundedJoinSemilattice (ShrinkingSet a) where
    bottom = ShrinkingSet $ S.fromList $ enumFromTo minBound maxBound

instance (Ord a, Enum a, Bounded a) => Based (ShrinkingSet a) a where
    jirelement a = ShrinkingSet $ S.delete a (shrinkingSet bottom)

propagateShrink :: (Ord a, Ord b) => (a -> b) -> ShrinkingSet a -> ShrinkingSet b
propagateShrink f = ShrinkingSet . S.map f . shrinkingSet

--
data Same a = Unknown | Unambiguous a | Ambiguous (Set a)

deriving instance Show a => Show (Same a)
deriving instance Eq a => Eq (Same a)

instance IsString a => IsString (Same a) where
    fromString = Unambiguous . fromString

instance Ord a => PartialOrd (Same a) where
    Unknown +> Unknown = True
    Unknown +> _ = False
    _ +> Unknown = True
    Unambiguous a1 +> Unambiguous a2 = a1 == a2
    Ambiguous s1 +> Ambiguous s2 = s1 >= s2
    Ambiguous s1 +> _ = True
    _ +> Ambiguous s2 = True

instance Ord a => JoinSemilattice (Same a) where
    Unknown \/ p = p
    p \/ Unknown = p
    Ambiguous as \/ Unambiguous a = Ambiguous (S.insert a as) 
    Unambiguous a \/ Ambiguous as = Ambiguous (S.insert a as) 
    Ambiguous as1 \/ Ambiguous as2 = Ambiguous (S.union as1 as2)
    p@(Unambiguous a1) \/ (Unambiguous a2)
        | a1 == a2 = p
        | otherwise = Ambiguous (S.fromList [a1, a2])

instance Ord a => BoundedJoinSemilattice (Same a) where
    bottom = Unknown

instance Ord a => Based (Same a) a where
    jirelement = Unambiguous


propagateSame :: (Ord a, Ord b) => (a -> b) -> Same a -> Same b
propagateSame f Unknown = Unknown
propagateSame f (Unambiguous a) = Unambiguous (f a)
propagateSame f (Ambiguous as) = Ambiguous (S.map f as)

-- higher kinded join semilattices

--
instance PartialOrd a => PartialOrd (Identity a) where
    Identity a1 +> Identity a2 = a1 +> a2

instance JoinSemilattice a => JoinSemilattice (Identity a) where
    Identity a1 \/ Identity a2 = Identity $ a1 \/ a2

instance BoundedJoinSemilattice a => BoundedJoinSemilattice (Identity a) where
    bottom = Identity bottom

instance Based a b => Based (Identity a) b where
    jirelement = Identity . jirelement

--
instance PartialOrd a => PartialOrd (Maybe a) where
    Nothing +> Nothing = True
    Nothing +> _ = False
    _ +> Nothing = True
    Just a +> Just b = a +> b

instance JoinSemilattice a => JoinSemilattice (Maybe a) where
    Nothing \/ ma = ma
    ma \/ Nothing = ma
    Just a \/ Just b = Just (a \/ b)

instance JoinSemilattice a => BoundedJoinSemilattice (Maybe a) where
    bottom = Nothing

instance JoinSemilattice a => Based (Maybe a) a where
    jirelement = Just

propagateMaybe :: BoundedJoinSemilattice a => Maybe a -> a -- homomorphism
propagateMaybe Nothing = bottom
propagateMaybe (Just a) = a

propagateIsJust :: JoinSemilattice a => Maybe a -> Increasing Bool -- homomorphism
propagateIsJust = Increasing . isJust

propagateIsNothing :: JoinSemilattice a => Maybe a -> Decreasing Bool -- homomorphism
propagateIsNothing = Decreasing . isNothing

--
newtype GrowingMap k v = GrowingMap { growingMap :: M.Map k v}

deriving instance (Show k, Show v) => Show (GrowingMap k v)
deriving instance (Eq k, Eq a) => Eq (GrowingMap k a)


instance (Ord k, PartialOrd v) => PartialOrd (GrowingMap k v) where
    GrowingMap m1 +> GrowingMap m2 = M.isSubmapOfBy (<+) m2 m1

instance (Ord k, JoinSemilattice v) => JoinSemilattice (GrowingMap k v) where
    GrowingMap m1 \/ GrowingMap m2 = GrowingMap $ M.unionWith (\/) m1 m2

instance (Ord k, BoundedJoinSemilattice v) => BoundedJoinSemilattice (GrowingMap k v) where
    bottom = GrowingMap mempty

instance (Ord k, BoundedJoinSemilattice v) => Based (GrowingMap k v) (k, v) where
    jirelement (k, v) = GrowingMap $ M.singleton k v

propagateMap :: (Ord k, BoundedJoinSemilattice s, BoundedJoinSemilattice s') => Homo s s' -> Homo (GrowingMap k s) (GrowingMap k s')
propagateMap h = Homo $ GrowingMap . fmap (homo h) . growingMap

propagateMapEntry :: (Ord k, BoundedJoinSemilattice s) => k -> Homo (GrowingMap k s) s
propagateMapEntry k = Homo $ fromMaybe bottom . M.lookup k . growingMap

propagateMapKeys :: (Ord k, BoundedJoinSemilattice s) => Homo (GrowingMap k s) (GrowingSet k)
propagateMapKeys = Homo $ GrowingSet . M.keysSet . growingMap

propagateMapValues :: (Ord k, BoundedJoinSemilattice s) => Homo (GrowingMap k s) s
propagateMapValues = Homo $ L.foldl (\/) bottom . growingMap



--
-- instance JoinSemilattice a => JoinSemilattice [a] where
--     l1 \/ l2 = foldl1 (\/) <$> transpose [l1, l2]

-- instance BoundedJoinSemilattice a => BoundedJoinSemilattice [a] where
--     bottom = mempty

-- instance Based a b => Based [a] (Int, b) where
--     jirelement (n, b) = replicate n bottom <> [jirelement b]


-- propagateListElement :: BoundedJoinSemilattice a => Int -> [a] -> a
-- propagateListElement i l 
--   | i >= length l = bottom
--   | otherwise = l !! i

-- 
instance (PartialOrd a, PartialOrd b) => PartialOrd (a, b) where
    (a1, b1) +> (a2, b2) = a1 +> a2 &&  b1 +> b2

instance (JoinSemilattice a, JoinSemilattice b) => JoinSemilattice (a, b) where
    (a1, b1) \/ (a2, b2) = (a1 \/ a2, b1 \/ b2)

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
-- instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c) => JoinSemilattice (a, b, c) where
--     (a1, b1, c1) \/ (a2, b2, c2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2)

-- instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b, BoundedJoinSemilattice c) => BoundedJoinSemilattice (a, b, c) where
--     bottom = (bottom, bottom, bottom)

-- instance (Based a b, Based c d, Based e f) => Based (a, c, e) (b, d, f) where
--     jirelement (b, d, f) = (jirelement b, jirelement d, jirelement f) 

--
-- instance (JoinSemilattice a, JoinSemilattice b, JoinSemilattice c, JoinSemilattice d) => JoinSemilattice (a, b, c, d) where
--     (a1, b1, c1, d1) \/ (a2, b2, c2, d2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2, d1 \/ d2)

-- instance (BoundedJoinSemilattice a, BoundedJoinSemilattice b, BoundedJoinSemilattice c, BoundedJoinSemilattice d) => BoundedJoinSemilattice (a, b, c, d) where
--     bottom = (bottom, bottom, bottom, bottom)

-- instance (Based a b, Based c d, Based e f, Based g h) => Based (a, c, e, g) (b, d, f, h) where
--     jirelement (b, d, f, h) = (jirelement b, jirelement d, jirelement f, jirelement h) 

-- and so on...

--
instance (PartialOrd a, PartialOrd b) => PartialOrd (Either a b) where
    Left a1 +> Left a2 = a1 +> a2
    Right a1 +> Right a2 = a1 +> a2
    Left _ +> Right _ = False
    Right _ +> Left _ = True


instance (JoinSemilattice a, JoinSemilattice b) => JoinSemilattice (Either a b) where
    Left a1 \/ Left a2 = Left (a1 \/ a2)
    Right b1 \/ Right b2 = Right (b1 \/ b2)
    Left _ \/ r@(Right _) = r
    r@(Right _) \/ Left _ = r

instance (BoundedJoinSemilattice a, JoinSemilattice b) => BoundedJoinSemilattice (Either a b) where
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
