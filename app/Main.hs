module Main where

import Semilattice
import Data.Time
import Data.Time.Format
import Data.Set
import Data.List
import qualified Data.Map as M
import Data.Semigroup

-- | Example

-- Can we have a semilattice Container where
-- a) container location is changing
-- b) container content is changing

data Container p = Container {
    containerPath :: Path,
    containerContent :: Content p
} deriving (Show, Eq)

instance Ord p => Semigroup (Container p) where
    (Container l1 c1) <> (Container l2 c2) = Container (l1 <> l2) (c1 <> c2)

instance Ord p => Monoid (Container p) where
    mempty = Container mempty mempty 

instance (Ord p, Eq p) => Semilattice (Container p)


data L = LA | LB | LC deriving (Show, Eq)

data Path = Path {
    pathLocs :: [L]
} deriving (Show, Eq)

instance Semigroup Path where
    (Path ls1) <> (Path ls2) = Path $ nub $ ls1 <> ls2

instance Monoid Path where 
    mempty = Path mempty

instance Semilattice Path


data Content p = Content {
    contentMap :: SMap (p, String) (Max Int)
} deriving (Show, Eq)

instance Ord p => Semigroup (Content p) where
    (Content map1) <> (Content map2) = Content $ map1 <> map2

instance Ord p => Monoid (Content p) where
    mempty = Content mempty

instance (Eq p, Ord p) => Semilattice (Content p)

-- events/goals
location :: Ord p => L -> Container p
location l = Container (Path [l]) mempty

content :: p -> String -> Int -> Container p
content p s i = Container mempty (Content (SMap (M.singleton (p, s) (Max i))))

main :: IO ()
main = do
    let state = location LB <> content 1 "coke" 3 <> content 2 "fanta" 8 <> location LA <> content 3 "pepsi" 7 <> content 1 "coke" 5
    let goal = content 1 "coke" 4 <> content 3 "pepsi" 6 <> location LB
    print $ isAchieved goal state
    print state
