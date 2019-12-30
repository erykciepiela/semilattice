module Main where

import JoinSemilattice
import Data.Map as M
import Data.Set as S
import Data.Map.Append
import Data.Semigroup
import ORSet

-- Can we have a semilattice container where
-- a) container location is changing
-- b) container content is changing
-- ContainerS stands for Container semilattice
data ContainerS p = ContainerS {
    containerPath :: S.Set Location,
    containerPositionContent :: AppendMap (p, String) (Max Int),
    containerLining :: Max Bool
} deriving Show

instance Ord p => Semigroup (ContainerS p) where
    (ContainerS p1 c1 l1) <> (ContainerS p2 c2 l2) = ContainerS (p1 <> p2) (c1 <> c2) (l1 <> l2)

instance Ord p => JoinSemilattice (ContainerS p)

data Location = LA | LB | LC deriving (Show, Eq, Ord)

-- events/goals
location :: Ord p => Location -> ContainerS p
location l = ContainerS (S.singleton l) mempty mempty

content :: p -> String -> Int -> ContainerS p
content p s i = ContainerS mempty (AppendMap (M.singleton (p, s) (Max i))) mempty

lining :: Ord p => ContainerS p
lining = ContainerS mempty mempty (Max True)

main :: IO ()
main = do
    --  print $ grow [DoNothing, Add 1, Add 2, Add 3, DoNothing] (S.empty :: S.Set Int)
    --  print $ ORSet.lookup 5 $ remove' 5 <> add' "tag" 5
    --  print $ ORSet.lookup 5 $ add' "tag" 5 <> remove' 5
    --  print $ ORSet.lookup 5 $ (remove 5 . add "tag" 5) initial
    --  print $ ORSet.lookup 5 $ (add "tag" 5 . remove 5) initial
    --  print $ ORSet.lookup 5 $ add "tag" 5 initial <> remove 5 initial -- should be False
    --  print $ ORSet.lookup 5 $ remove 5 initial <> add "tag" 5 initial -- should be False
     let f = remove 6
     let g = remove 5
     print$ initial <+ f initial
     print $ f initial <+ f (g initial)
     print $ ORSet.lookup 5 $ remove 5 initial <> add "1" 5 initial