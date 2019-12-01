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

data Container = Container {
    containerPath :: Path,
    containerContent :: Content
} deriving (Show, Eq)

instance Semigroup Container where
    (Container l1 c1) <> (Container l2 c2) = Container (l1 <> l2) (c1 <> c2)

instance Monoid Container where
    mempty = Container mempty mempty 

instance Semilattice Container


data L = LA | LB | LC deriving (Show, Eq)

data Path = Path {
    pathLocs :: [L]
} deriving (Show, Eq)

instance Semigroup Path where
    (Path ls1) <> (Path ls2) = Path $ nub $ ls1 <> ls2

instance Monoid Path where 
    mempty = Path mempty

instance Semilattice Path


data Content = Content {
    contentMap :: SMap String (Max Int)
} deriving (Show, Eq)

instance Semigroup Content where
    (Content map1) <> (Content map2) = Content $ map1 <> map2

instance Monoid Content where
    mempty = Content mempty

instance Semilattice Content

-- events/goals
location :: L -> Container
location l = Container (Path [l]) mempty

content :: String -> Int -> Container
content s i = Container mempty (Content (SMap (M.singleton s (Max i))))

main :: IO ()
main = do
    let state = location LB <> content "coke" 3 <> content "fanta" 8 <> location LA <> content "pepsi" 7 <> content "coke" 5
    let goal = content "coke" 4 <> content "pepsi" 6 <> location LB
    print $ isAchieved goal state
