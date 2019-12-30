module ORSet where

import           Prelude hiding (lookup)

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (Semigroup, (<>))
import           Numeric.Natural (Natural)
import           JoinSemilattice

type Tag = (String, Natural)

newtype ORSet a = ORSet (Map a (Map Tag Bool))
    deriving (Eq, Show)

unpack :: ORSet a -> Map a (Map Tag Bool)
unpack (ORSet s) = s

instance Ord a => Semigroup (ORSet a) where
    ORSet s1 <> ORSet s2 = ORSet $ Map.unionWith (Map.unionWith (&&)) s1 s2

instance Ord a => JoinSemilattice (ORSet a)

initial :: ORSet a
initial = ORSet Map.empty

add :: (Ord a) => String -> a -> ORSet a -> ORSet a
add pid a (ORSet s) = ORSet $ Map.alter (add1 pid) a s
    where
    add1 :: (Ord a, Ord b, Num b) => a -> Maybe (Map (a, b) Bool) -> Maybe (Map (a, b) Bool)
    add1 pid = Just . add2 pid . fromMaybe Map.empty
    add2 pid tags = Map.insert (pid, fromIntegral $ length tags) True tags

remove :: Ord a => a -> ORSet a -> ORSet a
remove a (ORSet s) = ORSet $ Map.adjust (Map.map $ const False) a s

lookup :: Ord a => a -> ORSet a -> Bool
lookup e = or . fromMaybe Map.empty . Map.lookup e . unpack    
