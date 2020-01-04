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

-- join semilattices
type PhysicalBag = S.Map Batch (S.Max Qty)

type PhysicalDT = (PhysicalBag, PhysicalBag, PhysicalBag)

type PhysicalDTs = S.Map LPN PhysicalDT

type DTAssignment = S.Map LogicalDTId (S.Value LPN)

type PhysicalState = (DTAssignment, PhysicalDTs)

type LogicalBag = S.Map SkuId (S.Max Qty)

type LogicalDT = (LogicalBag, LogicalBag, LogicalBag)

type LogicalState = S.Map LogicalDTId LogicalDT

-- propagators
physicalBag :: PickId -> SkuId -> Qty -> PhysicalBag
physicalBag pickId skuId qty = S.map (pickId, skuId) (S.max qty)

dtAssignment :: LogicalDTId -> LPN -> DTAssignment
dtAssignment dtid lpn = S.map dtid (S.Value lpn)

logicalBag :: SkuId -> Qty -> LogicalBag
logicalBag skuId qty = AppendMap $ M.singleton skuId (Max qty)

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

logicalDTtoState :: LogicalDTId -> LogicalDT -> LogicalState
logicalDTtoState dtId dt = AppendMap $ M.singleton dtId dt

dtAssignmentToPhysicalState :: DTAssignment -> PhysicalState
dtAssignmentToPhysicalState a = (a, mempty)

--
main :: IO ()
main = do
    let actualPhysical = mconcat [ dtAssignment' "1" "123", physicalPick "123" 0 "1" "apple" 3, physicalPick "123" 1 "2" "banana" 4, physicalPick "123" 0 "3" "coconut" 1, physicalPick "123" 0 "4" "coconut" 2, physicalPick "123" 2 "5" "donut" 5, physicalPick "123" 2 "5" "donut" 5, dtAssignment' "2" "444", physicalPick "444" 0 "6" "cucumber" 7]
    let actualLogical = physicalToLogicalState actualPhysical
    let expectedLogic = mconcat [logicalPick "1" 0 "apple" 3, logicalPick "1" 1 "banana" 4]
    print $ actualLogical S.+> expectedLogic -- True
    print $ actualLogical S.<+ expectedLogic -- False 
        where
            physicalPick :: LPN -> BagId -> PickId -> SkuId -> Qty -> PhysicalState
            physicalPick lpn bagId pickId skuId = physicalDTtoState lpn . physicalBagToDT bagId . physicalBag pickId skuId
            logicalPick :: LogicalDTId -> BagId -> SkuId -> Qty -> LogicalState
            logicalPick dtId bagId skuId = logicalDTtoState dtId . logicalBagToDT bagId . logicalBag skuId
            dtAssignment' :: LogicalDTId -> LPN -> PhysicalState
            dtAssignment' dtid lpn = dtAssignmentToPhysicalState $ dtAssignment dtid lpn




