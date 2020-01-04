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
type PhysicalBag = AppendMap Batch (S.Increasing Qty)

type PhysicalDT = (PhysicalBag, PhysicalBag, PhysicalBag)

type PhysicalDTs = AppendMap LPN PhysicalDT

type DTAssignment = AppendMap LogicalDTId (S.Same LPN)

type PhysicalState = (DTAssignment, PhysicalDTs)

type LogicalBag = AppendMap SkuId (S.Increasing Qty)

type LogicalDT = (LogicalBag, LogicalBag, LogicalBag)

type LogicalState = AppendMap LogicalDTId LogicalDT

-- propagators
physicalBag :: PickId -> SkuId -> Qty -> PhysicalBag
physicalBag pickId skuId qty = AppendMap $ M.singleton  (pickId, skuId) (S.Increasing qty)

dtAssignment :: LogicalDTId -> LPN -> DTAssignment
dtAssignment dtid lpn = AppendMap $ M.singleton dtid (S.Unambiguous lpn)

logicalBag :: SkuId -> Qty -> LogicalBag
logicalBag skuId qty = AppendMap $ M.singleton skuId (S.Increasing qty)

physicalToLogicalBag :: PhysicalBag -> LogicalBag
physicalToLogicalBag b = AppendMap $ mapKeysWith (\max1 max2 -> S.Increasing $ S.increasing max1 + S.increasing max2) snd $ unAppendMap b

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
physicalToLogicalState (assignments, p) = AppendMap $ (\slpn -> case slpn of
    S.Unknown -> mempty
    S.Ambiguous _ -> mempty 
    (S.Unambiguous lpn) -> maybe mempty physicalTologicalDT (M.lookup lpn (unAppendMap p))) <$> (unAppendMap assignments)

physicalDTtoState :: LPN -> PhysicalDT -> PhysicalState
physicalDTtoState lpn dt = (mempty, AppendMap $ M.singleton lpn dt)

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




