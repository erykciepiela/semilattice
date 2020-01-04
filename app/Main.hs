module Main where

import qualified JoinSemilattice as S
import Data.Map as M
import Data.Map.Append
import Data.Semigroup
import Data.Maybe

type PickId = String
type SkuId = String
type Qty = Int
type Batch = (String, SkuId)
type LPN = String
type DTLogicalId = String

type Bag = S.Map Batch (S.Max Qty)

bag :: PickId -> SkuId -> Qty -> Bag
bag pickId skuId qty = S.map (pickId, skuId) (S.max qty)

--
type LogicalBag = S.Map SkuId (S.Max Qty)

-- propagator
logicalBag :: Bag -> LogicalBag
logicalBag b = AppendMap $ mapKeysWith (\max1 max2 -> Max $ getMax max1 + getMax max2) snd $ unAppendMap b


type DT = (Bag, Bag, Bag)

dt :: Int -> Bag -> DT
dt 0 b = (b, mempty, mempty)
dt 1 b = (mempty, b, mempty)
dt 2 b = (mempty, mempty, b)

--
type LogicalDT = (LogicalBag, LogicalBag, LogicalBag)

-- propagator
logicalDT :: DT -> LogicalDT
logicalDT (b1, b2, b3) = (logicalBag b1, logicalBag b2, logicalBag b3)

type State = (S.Map DTLogicalId (S.Value LPN), S.Map LPN DT)

picking :: LPN -> Int -> PickId -> SkuId -> Qty -> State
picking lpn bagId batchId skuId qty = picking' lpn $ dt bagId $ bag batchId skuId qty
    where
        picking' :: LPN -> DT -> State
        picking' lpn dt = (mempty, S.map lpn dt)

assigning :: DTLogicalId -> LPN -> State
assigning dtid lpn = (S.map dtid (S.Value lpn), mempty)

--
type LogicalDTs = S.Map DTLogicalId (S.Value LogicalDT)

-- propagator
logicalDTs :: State -> LogicalDTs
logicalDTs (assignments, p) = AppendMap $ (\plpn -> (\lpn -> maybe mempty logicalDT (M.lookup lpn (unAppendMap p))) <$> plpn) <$> unAppendMap assignments

main :: IO ()
main = print $ logicalDTs $ mconcat [
    assigning "1" "123", 
    picking "123" 0 "1" "apple" 3, 
    picking "123" 1 "2" "banana" 4, 
    picking "123" 0 "3" "coconut" 1, 
    picking "123" 0 "4" "coconut" 2, 
    picking "123" 2 "5" "donut" 5, 
    picking "123" 2 "5" "donut" 5,
    assigning "2" "444",
    picking "444" 0 "6" "cucumber" 7
    ]
