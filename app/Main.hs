module Main where

import Semilattice
import Data.Set as S
import qualified Data.Map as M
import Data.Semigroup

-- Can we have a semilattice container where
-- a) container location is changing
-- b) container content is changing
data Container p = Container {
    containerPath :: SSet Location,
    containerPositionContent :: SMap (p, String) (Max Int),
    containerLining :: Max Bool
} deriving (Show, Eq)

instance Ord p => Semigroup (Container p) where
    (Container p1 c1 l1) <> (Container p2 c2 l2) = Container (p1 <> p2) (c1 <> c2) (l1 <> l2)

instance (Ord p, Eq p) => Semilattice (Container p)

data Location = LA | LB | LC deriving (Show, Eq, Ord)

-- events/goals
location :: Ord p => Location -> Container p
location l = Container (SSet (S.singleton l)) mempty mempty

content :: p -> String -> Int -> Container p
content p s i = Container mempty (SMap (M.singleton (p, s) (Max i))) mempty

lining :: Ord p => Container p
lining = Container mempty mempty (Max True)

main :: IO ()
main = do
    let state = lining <> lining <> location LB <> content 1 "coke" 3 <> content 1 "coke" 3 <> content 2 "fanta" 6 <> location LA <> content 3 "pepsi" 7 <> lining <> content 1 "coke" 5
    let goal = lining <> content 1 "coke" 5 <> content 3 "pepsi" 7 <> content 2 "fanta" 6 <> location LB <> location LA
    print $ leads state (content 2 "fanta" 8) goal
    print $ isAchieved goal state
    print goal
    print state
