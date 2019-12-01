module Main where

import Semilattice
import Data.Map as M
import Data.Set as S
import Data.Map.Append
import Data.Semigroup

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

instance Ord p => Semilattice (ContainerS p)

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
    let state = lining <> lining <> location LB <> content 1 "coke" 3 <> content 1 "coke" 3 <> content 2 "fanta" 6 <> location LA <> content 3 "pepsi" 7 <> lining <> content 1 "coke" 5
    let goal = lining <> content 1 "coke" 5 <> content 3 "pepsi" 7 <> content 2 "fanta" 6 <> location LB <> location LA
    print goal
    print state

-- let goal' = Con {
--     conLocation = Just LB,
--     conPositionContent = M.fromList [((1, "coke"), 5)]
-- }
-- print $ leads state (content 2 "fanta" 8) goal
-- print $ isAchieved goal state

-- data Con p = Con {
--     conLocation :: Maybe Location,
--     conPositionContent :: M.Map (p, String) Int,
--     conLining :: Bool
-- }

-- con2con :: ContainerS p -> Con p
-- con2con c = Con {
--     conLocation = S.lookupMax (sset (containerPath c)),
--     conPositionContent = getMax <$> smap (containerPositionContent c),
--     conLining = getMax (containerLining c)
-- }
