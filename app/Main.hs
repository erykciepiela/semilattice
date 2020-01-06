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
type Bag = Map SkuId (Increasing Qty)

type DT = (Bag, Bag, Bag)

type DTs = Map LPN DT

type DTAssignment = Map LogicalDTId (Same LPN)

type PhysicalState = (DTAssignment, DTs)

type LogicalState = Map LogicalDTId DT

-- homomorphisms - morphisms
bag :: SkuId -> Qty -> Bag
bag skuId qty = base (skuId, Increasing qty)

bagToDT :: Int -> Bag -> DT
bagToDT 0 b = (b, bottom, bottom)
bagToDT 1 b = (bottom, b, bottom)
bagToDT 2 b = (bottom, bottom, b)

dtToPhysicalState :: LPN -> DT -> PhysicalState
dtToPhysicalState lpn dt = (bottom, base (lpn, dt))

physicalToLogicalState :: PhysicalState -> LogicalState
physicalToLogicalState (assignments, p) = (\slpn -> case slpn of
    Unknown -> bottom
    Ambiguous _ -> bottom 
    (Unambiguous lpn) -> fromMaybe bottom (M.lookup lpn p)) <$> assignments
-- this is not homorphism, it's merely monotonic

dtAssignment :: LogicalDTId -> LPN -> DTAssignment
dtAssignment dtid lpn = base (dtid, Unambiguous lpn)

dtAssignmentToPhysicalState :: DTAssignment -> PhysicalState
dtAssignmentToPhysicalState a = (a, bottom)

--
main :: IO ()
main = do
    let actual = bjsconcat [dtAssignment' "1" "123", physicalPick "123" 0 "apple" 3, physicalPick "123" 1 "banana" 4, physicalPick "123" 0 "coconut" 1, physicalPick "123" 0 "coconut" 2, physicalPick "123" 2 "donut" 5, physicalPick "123" 2 "donut" 5, dtAssignment' "2" "444", physicalPick "444" 0 "cucumber" 7]
    let expected = bjsconcat [logicalPick "1" 0 "apple" 3, logicalPick "1" 1 "banana" 4]
    print $ actual +> expected -- True
    print $ actual <+ expected -- False 
        where
            physicalPick :: LPN -> BagId -> SkuId -> Qty -> LogicalState
            physicalPick lpn bagId skuId = physicalToLogicalState . dtToPhysicalState lpn . bagToDT bagId . bag skuId
            logicalPick :: LogicalDTId -> BagId -> SkuId -> Qty -> LogicalState
            logicalPick dtId bagId skuId = physicalToLogicalState . dtToPhysicalState dtId . bagToDT bagId . bag skuId
            dtAssignment' :: LogicalDTId -> LPN -> LogicalState
            dtAssignment' dtid = physicalToLogicalState . dtAssignmentToPhysicalState . dtAssignment dtid
