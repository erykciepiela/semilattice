module Main where

import Semilattice
import Data.Time
import Data.Time.Format
import Data.Set
import Data.List
import qualified Data.Map as M

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
    contentMap :: MapMax String Qty
} deriving (Show, Eq)

instance Semigroup Content where
    (Content map1) <> (Content map2) = Content $ map1 <> map2

instance Monoid Content where
    mempty = Content mempty

instance Semilattice Content

-- data CountedItems = CountedItems {
--     countentItemsName :: String,
--     countedItemsQty :: Qty
-- }

newtype MapMax k v = MapMax { mapMax :: M.Map k v}

deriving instance (Show k, Show v) => Show (MapMax k v)

instance (Eq k, Eq v) => Eq (MapMax k v) where
    mm1 == mm2 = mapMax mm1 == mapMax mm2

instance (Ord k, Semigroup v) => Semigroup (MapMax k v) where
    mm1 <> mm2 = MapMax $ M.unionWith (<>) (mapMax mm1) (mapMax mm2)

instance (Ord k, Semigroup v) => Monoid (MapMax k v) where
    mempty = MapMax M.empty 

instance (Ord k, Eq k, Semilattice v) => Semilattice (MapMax k v)


-- instance (Eq k, Semilattice v) => Semilattice (MapMax k v) where

data Qty = Qty { qty :: Int } deriving (Show, Eq)

instance Semigroup Qty where
    q1 <> q2 = Qty $ max (qty q1) (qty q2)

instance Monoid Qty where
    mempty = Qty 0

instance Semilattice Qty

-- events
locationSet :: L -> Container
locationSet l = Container (Path [l]) mempty

contentAdded :: String -> Int -> Container
contentAdded s i = Container mempty (Content (MapMax (M.singleton s (Qty i))))

-- goals
content :: M.Map String Qty -> Container
content map = Container mempty (Content (MapMax map))

location :: L -> Container
location l = Container (Path [l]) mempty

main :: IO ()
main = do
    let state = mconcat [locationSet LB, contentAdded "coke" 3, locationSet LA, contentAdded "pepsi" 7]
    let goal = mconcat [content (M.fromList [("coke", Qty 2), ("pepsi", Qty 7)]), location LB]
    print $ isAchieved goal state
