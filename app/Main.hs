module Main where

import Semilattice
import Data.Map as M

type PickId = String
type SkuId = String
type Qty = Int
type LPN = String
type LogicalDTId = String
type BagId = Int

-- bounded join semilattices
type PhysicalBag = Map (PickId, SkuId) (Increasing Qty)

type PhysicalDT = (PhysicalBag, PhysicalBag, PhysicalBag)

type PhysicalDTs = Map LPN PhysicalDT

type DTAssignment = Map LogicalDTId (Same LPN)

type PhysicalState = (DTAssignment, PhysicalDTs)

type LogicalBag = Map SkuId (Increasing Qty)

type LogicalDT = (LogicalBag, LogicalBag, LogicalBag)

type LogicalState = Map LogicalDTId LogicalDT

-- homomorphisms
physicalBag :: PickId -> SkuId -> Qty -> PhysicalBag
physicalBag pickId skuId qty = base ((pickId, skuId), Increasing qty)

dtAssignment :: LogicalDTId -> LPN -> DTAssignment
dtAssignment dtid lpn = base (dtid, Unambiguous lpn)

logicalBag :: SkuId -> Qty -> LogicalBag
logicalBag skuId qty = base (skuId, Increasing qty)

physicalToLogicalBag :: PhysicalBag -> LogicalBag
physicalToLogicalBag = propagateMap (propagateIncrease2 (+)) snd

physicalBagToDT :: Int -> PhysicalBag -> PhysicalDT
physicalBagToDT 0 b = (b, bottom, bottom)
physicalBagToDT 1 b = (bottom, b, bottom)
physicalBagToDT 2 b = (bottom, bottom, b)

physicalTologicalDT :: PhysicalDT -> LogicalDT
physicalTologicalDT (b1, b2, b3) = (physicalToLogicalBag b1, physicalToLogicalBag b2, physicalToLogicalBag b3)

logicalBagToDT :: Int -> LogicalBag -> LogicalDT
logicalBagToDT 0 b = (b, bottom, bottom)
logicalBagToDT 1 b = (bottom, b, bottom)
logicalBagToDT 2 b = (bottom, bottom, b)

physicalToLogicalState :: PhysicalState -> LogicalState
physicalToLogicalState (assignments, p) = (\slpn -> case slpn of
    Unknown -> bottom
    Ambiguous _ -> bottom 
    (Unambiguous lpn) -> maybe bottom physicalTologicalDT (M.lookup lpn p)) <$> assignments

physicalDTtoState :: LPN -> PhysicalDT -> PhysicalState
physicalDTtoState lpn dt = (bottom, base (lpn, dt))

logicalDTtoState :: LogicalDTId -> LogicalDT -> LogicalState
logicalDTtoState dtId dt = base (dtId, dt)

dtAssignmentToPhysicalState :: DTAssignment -> PhysicalState
dtAssignmentToPhysicalState a = (a, bottom)

--
main :: IO ()
main = do
    let actualPhysical = mconcat [ dtAssignment' "1" "123", physicalPick "123" 0 "1" "apple" 3, physicalPick "123" 1 "2" "banana" 4, physicalPick "123" 0 "3" "coconut" 1, physicalPick "123" 0 "4" "coconut" 2, physicalPick "123" 2 "5" "donut" 5, physicalPick "123" 2 "5" "donut" 5, dtAssignment' "2" "444", physicalPick "444" 0 "6" "cucumber" 7]
    let actualLogical = physicalToLogicalState actualPhysical
    let expectedLogic = mconcat [logicalPick "1" 0 "apple" 3, logicalPick "1" 1 "banana" 4]
    print $ actualLogical +> expectedLogic -- True
    print $ actualLogical <+ expectedLogic -- False 
        where
            physicalPick :: LPN -> BagId -> PickId -> SkuId -> Qty -> PhysicalState
            physicalPick lpn bagId pickId skuId = physicalDTtoState lpn . physicalBagToDT bagId . physicalBag pickId skuId
            logicalPick :: LogicalDTId -> BagId -> SkuId -> Qty -> LogicalState
            logicalPick dtId bagId skuId = logicalDTtoState dtId . logicalBagToDT bagId . logicalBag skuId
            dtAssignment' :: LogicalDTId -> LPN -> PhysicalState
            dtAssignment' dtid lpn = dtAssignmentToPhysicalState $ dtAssignment dtid lpn
