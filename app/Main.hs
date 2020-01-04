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
type LogicalDTId = String
type BagId = Int

-- join semilattice
type PhysicalBag = S.Map Batch (S.Max Qty)

physicalBag :: PickId -> SkuId -> Qty -> PhysicalBag
physicalBag pickId skuId qty = S.map (pickId, skuId) (S.max qty)

-- join semilattice
type PhysicalDT = (PhysicalBag, PhysicalBag, PhysicalBag)

-- join semilattice
type PhysicalState = (S.Map LogicalDTId (S.Value LPN), S.Map LPN PhysicalDT)

dtAssignment :: LogicalDTId -> LPN -> PhysicalState
dtAssignment dtid lpn = (S.map dtid (S.Value lpn), mempty)

dtPick :: LPN -> BagId -> PickId -> SkuId -> Qty -> PhysicalState
dtPick lpn bagId pickId skuId = physicalDTtoState lpn . physicalBagToDT bagId . physicalBag pickId skuId

-- join semilattice
type LogicalBag = S.Map SkuId (S.Max Qty)

logicalBag :: SkuId -> Qty -> LogicalBag
logicalBag skuId qty = AppendMap $ M.singleton skuId (Max qty)

-- join semilattice
type LogicalDT = (LogicalBag, LogicalBag, LogicalBag)

-- join semilattice
type LogicalState = S.Map LogicalDTId LogicalDT

logicalPick :: LogicalDTId -> BagId -> SkuId -> Qty -> LogicalState
logicalPick dtId bagId skuId qty = AppendMap $ M.singleton dtId $ logicalBagToDT bagId $ logicalBag skuId qty

-- propagators
physicalToLogicalBag :: PhysicalBag -> LogicalBag
physicalToLogicalBag b = AppendMap $ mapKeysWith (\max1 max2 -> Max $ getMax max1 + getMax max2) snd $ unAppendMap b

physicalBagToDT :: Int -> PhysicalBag -> PhysicalDT
physicalBagToDT 0 b = (b, mempty, mempty)
physicalBagToDT 1 b = (mempty, b, mempty)
physicalBagToDT 2 b = (mempty, mempty, b)

physicalTologicalDT :: PhysicalDT -> LogicalDT
physicalTologicalDT (b1, b2, b3) = (physicalToLogicalBag b1, physicalToLogicalBag b2, physicalToLogicalBag b3)

logicalBagToDT :: Int -> LogicalBag -> LogicalDT
logicalBagToDT 0 b = (b, mempty, mempty)
logicalBagToDT 1 b = (mempty, b, mempty)
logicalBagToDT 2 b = (mempty, mempty, b)

physicalToLogicalState :: PhysicalState -> LogicalState
physicalToLogicalState (assignments, p) = AppendMap $ (\lpn -> maybe mempty physicalTologicalDT (M.lookup lpn (unAppendMap p))) <$> M.mapMaybe S.getValue (unAppendMap assignments)

physicalDTtoState :: LPN -> PhysicalDT -> PhysicalState
physicalDTtoState lpn dt = (mempty, S.map lpn dt)

physicalBagToState :: LPN -> Int -> PhysicalBag -> PhysicalState
physicalBagToState lpn bagId = physicalDTtoState lpn . physicalBagToDT bagId


--
main :: IO ()
main = do
    let actualPhysical = mconcat [ dtAssignment "1" "123", dtPick "123" 0 "1" "apple" 3, dtPick "123" 1 "2" "banana" 4, dtPick "123" 0 "3" "coconut" 1, dtPick "123" 0 "4" "coconut" 2, dtPick "123" 2 "5" "donut" 5, dtPick "123" 2 "5" "donut" 5, dtAssignment "2" "444", dtPick "444" 0 "6" "cucumber" 7]
    let actualLogical = physicalToLogicalState actualPhysical
    let expectedLogic = mconcat [logicalPick "1" 0 "apple" 3, logicalPick "1" 1 "banana" 4]
    print $ actualLogical S.+> expectedLogic -- True
    print $ actualLogical S.<+ expectedLogic -- False 
