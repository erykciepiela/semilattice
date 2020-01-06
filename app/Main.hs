module Main where

import Semilattice
import Data.Map as M
import Data.Maybe

type SkuId = String
type Qty = Int
type LPN = String
type LogicalDTId = String
type BagId = Int

-- bounded join semilattices - objects
type PhysicalBag = Map SkuId (Increasing Qty)

type PhysicalDT = (PhysicalBag, PhysicalBag, PhysicalBag)

type PhysicalDTs = Map LPN PhysicalDT

type DTAssignment = Map LogicalDTId (Same LPN)

type PhysicalState = (DTAssignment, PhysicalDTs)

type LogicalState = Map LogicalDTId PhysicalDT

-- homomorphisms - morphisms
physicalBag :: SkuId -> Qty -> PhysicalBag
physicalBag skuId qty = base (skuId, Increasing qty)

dtAssignment :: LogicalDTId -> LPN -> DTAssignment
dtAssignment dtid lpn = base (dtid, Unambiguous lpn)

physicalBagToDT :: Int -> PhysicalBag -> PhysicalDT
physicalBagToDT 0 b = (b, bottom, bottom)
physicalBagToDT 1 b = (bottom, b, bottom)
physicalBagToDT 2 b = (bottom, bottom, b)

physicalToLogicalState :: PhysicalState -> LogicalState
physicalToLogicalState (assignments, p) = (\slpn -> case slpn of
    Unknown -> bottom
    Ambiguous _ -> bottom 
    (Unambiguous lpn) -> fromMaybe bottom (M.lookup lpn p)) <$> assignments

physicalDTtoState :: LPN -> PhysicalDT -> PhysicalState
physicalDTtoState lpn dt = (bottom, base (lpn, dt))

-- logicalDTtoState :: LogicalDTId -> LogicalDT -> LogicalState
-- logicalDTtoState dtId dt = base (dtId, dt)

dtAssignmentToPhysicalState :: DTAssignment -> PhysicalState
dtAssignmentToPhysicalState a = (a, bottom)

--
main :: IO ()
main = do
    let actualPhysical = mconcat [ dtAssignment' "1" "123", physicalPick "123" 0 "apple" 3, physicalPick "123" 1 "banana" 4, physicalPick "123" 0 "coconut" 1, physicalPick "123" 0 "coconut" 2, physicalPick "123" 2 "donut" 5, physicalPick "123" 2 "donut" 5, dtAssignment' "2" "444", physicalPick "444" 0 "cucumber" 7]
    let actualLogical = physicalToLogicalState actualPhysical
    let expectedLogic = mconcat [logicalPick "1" 0 "apple" 3, logicalPick "1" 1 "banana" 4]
    print $ actualLogical +> expectedLogic -- True
    print $ actualLogical <+ expectedLogic -- False 
        where
            physicalPick :: LPN -> BagId -> SkuId -> Qty -> PhysicalState
            physicalPick lpn bagId skuId = physicalDTtoState lpn . physicalBagToDT bagId . physicalBag skuId
            logicalPick :: LogicalDTId -> BagId -> SkuId -> Qty -> LogicalState
            logicalPick dtId bagId skuId = physicalToLogicalState . physicalDTtoState dtId . physicalBagToDT bagId . physicalBag skuId
            dtAssignment' :: LogicalDTId -> LPN -> PhysicalState
            dtAssignment' dtid lpn = dtAssignmentToPhysicalState $ dtAssignment dtid lpn
