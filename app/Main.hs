module Main where

import qualified JoinSemilattice as S
import Data.Map as M
import Data.Map.Append
import Data.Semigroup
import Data.Maybe
import Data.Set as Set

type PickId = String
type SkuId = String
type Qty = Int
type Batch = (String, SkuId)
type LPN = String
type DTLogicalId = String
type BagId = Int

type Bag = S.Map Batch (S.Max Qty)

bag :: PickId -> SkuId -> Qty -> Bag
bag pickId skuId qty = S.map (pickId, skuId) (S.max qty)

--
type LogicalBag = S.Map SkuId (S.Max Qty)

lb :: SkuId -> Qty -> LogicalBag
lb skuId qty = AppendMap $ M.singleton skuId (Max qty)

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

dt' :: Int -> LogicalBag -> LogicalDT
dt' 0 b = (b, mempty, mempty)
dt' 1 b = (mempty, b, mempty)
dt' 2 b = (mempty, mempty, b)


-- propagator
logicalDT :: DT -> LogicalDT
logicalDT (b1, b2, b3) = (logicalBag b1, logicalBag b2, logicalBag b3)

type PhysicalState = (S.Map DTLogicalId (S.Value LPN), S.Map LPN DT)

dtPick :: LPN -> Int -> PickId -> SkuId -> Qty -> PhysicalState
dtPick lpn bagId batchId skuId qty = (mempty, S.map lpn (dt bagId $ bag batchId skuId qty))

dtAssignment :: DTLogicalId -> LPN -> PhysicalState
dtAssignment dtid lpn = (S.map dtid (S.Value lpn), mempty)

--
type LogicalState = S.Map DTLogicalId LogicalDT

-- propagator
logicalState :: PhysicalState -> LogicalState
-- logicalState (assignments, p) = AppendMap $ fmap (\lpn -> maybe mempty logicalDT (M.lookup lpn (unAppendMap p))) <$> unAppendMap assignments
logicalState (assignments, p) = AppendMap $ (\lpn -> maybe mempty logicalDT (M.lookup lpn (unAppendMap p))) <$> M.mapMaybe S.getValue (unAppendMap assignments)

-- ctor
logicalPick :: DTLogicalId -> BagId -> SkuId -> Qty -> LogicalState
logicalPick dtId bagId skuId qty = AppendMap $ M.singleton dtId $ dt' bagId $ lb skuId qty


main :: IO ()
main = do
    let actualPhysical = mconcat [ dtAssignment "1" "123", dtPick "123" 0 "1" "apple" 3, dtPick "123" 1 "2" "banana" 4, dtPick "123" 0 "3" "coconut" 1, dtPick "123" 0 "4" "coconut" 2, dtPick "123" 2 "5" "donut" 5, dtPick "123" 2 "5" "donut" 5, dtAssignment "2" "444", dtPick "444" 0 "6" "cucumber" 7]
    let actualLogical = logicalState actualPhysical
    let expectedLogic = mconcat [logicalPick "1" 0 "apple" 3, logicalPick "1" 1 "banana" 4]
    print $ actualLogical S.+> expectedLogic -- True
    print $ actualLogical S.<+ expectedLogic -- False 
