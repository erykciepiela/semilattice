module ORSet where

import           Prelude hiding (lookup)

-- import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (Semigroup, (<>))
import           Numeric.Natural (Natural)
import           JoinSemilattice

type Tag = (String, Natural)

newtype ORSet a = ORSet (M.Map a (M.Map Tag Bool))
    deriving (Eq, Show)

unpack :: ORSet a -> M.Map a (M.Map Tag Bool)
unpack (ORSet s) = s

instance Ord a => Semigroup (ORSet a) where
    ORSet s1 <> ORSet s2 = ORSet $ M.unionWith (M.unionWith (&&)) s1 s2

instance Ord a => JoinSemilattice (ORSet a)

initial :: ORSet a
initial = ORSet M.empty

add :: (Ord a) => String -> a -> ORSet a -> ORSet a
add pid a (ORSet s) = ORSet $ M.alter (add1 pid) a s
    where
    add1 :: (Ord a, Ord b, Num b) => a -> Maybe (M.Map (a, b) Bool) -> Maybe (M.Map (a, b) Bool)
    add1 pid = Just . add2 pid . fromMaybe M.empty
    add2 pid tags = M.insert (pid, fromIntegral $ length tags) True tags

remove :: Ord a => a -> ORSet a -> ORSet a
remove a (ORSet s) = ORSet $ M.adjust (M.map $ const False) a s

lookup :: Ord a => a -> ORSet a -> Bool
lookup e = or . fromMaybe M.empty . M.lookup e . unpack    
