module Main where

import Semilattice
import Data.Map as M
import Data.Maybe

type SkuId = String
type Qty = Int
type LPN = String
type LogicalDTId = String
type BagId = Int
type ShipmentId = String
type VanId = String
type FrameId = String
type PositionInFrame = Int
type PositionInVan = Int
type PositionInShipment = Int
-- type FrameId = String

-- bounded join semilattices - objects
type Bag = Map SkuId (Increasing Qty)

type DT = (Bag, Bag, Bag)

type Frame = Map PositionInFrame (Same LPN, DT)

type Van = Map PositionInVan (Same LPN, Frame)

type Shipment = Map PositionInShipment (Same LPN, Van)

type FrameGoal = Map PositionInFrame DT
type VanGoal = Map PositionInVan FrameGoal
type ShipmentGoal = Map PositionInShipment VanGoal

type DTs = Map LPN DT

type DTAssignment = Map LogicalDTId (Same LPN)

type PhysicalState = (DTAssignment, DTs)

type LogicalState = Map LogicalDTId DT

-- functions
foo :: Frame -> Map LPN PositionInFrame
foo = undefined

-- homomorphisms - morphisms
pick :: PositionInShipment -> PositionInVan -> PositionInFrame -> LPN -> Int -> SkuId -> Qty -> Shipment
pick pishipment pivan piframe dtlpn 0 skuId qty = base (pishipment, (bottom, base (pivan, (bottom, base (piframe, (Unambiguous dtlpn, (base (skuId, Increasing qty), bottom, bottom)))))))
pick pishipment pivan piframe dtlpn 1 skuId qty = base (pishipment, (bottom, base (pivan, (bottom, base (piframe, (Unambiguous dtlpn, (bottom, base (skuId, Increasing qty), bottom)))))))
pick pishipment pivan piframe dtlpn 2 skuId qty = base (pishipment, (bottom, base (pivan, (bottom, base (piframe, (Unambiguous dtlpn, (bottom, bottom, base (skuId, Increasing qty))))))))

frameAssign :: PositionInShipment -> PositionInVan -> LPN -> Shipment
frameAssign pishipment pivan frameLpn = base (pishipment, (bottom, base (pivan, (Unambiguous frameLpn, bottom))))

vanAssign :: PositionInShipment -> LPN -> Shipment
vanAssign pishipment vanLpn = base (pishipment, (Unambiguous vanLpn, bottom))

frameToGoal :: Frame -> FrameGoal
frameToGoal = fmap snd

vanToGoal :: Van -> VanGoal
vanToGoal = fmap $ frameToGoal . snd

shipmentToGoal :: Shipment -> ShipmentGoal
shipmentToGoal = fmap $ vanToGoal . snd

pickGoal :: PositionInShipment -> PositionInVan -> PositionInFrame -> Int -> SkuId -> Qty -> ShipmentGoal
pickGoal pishipment pivan piframe 0 skuId qty = base (pishipment, base (pivan, base (piframe, (base (skuId, Increasing qty), bottom, bottom))))
pickGoal pishipment pivan piframe 1 skuId qty = base (pishipment, base (pivan, base (piframe, (bottom, base (skuId, Increasing qty), bottom))))
pickGoal pishipment pivan piframe 2 skuId qty = base (pishipment, base (pivan, base (piframe, (bottom, bottom, base (skuId, Increasing qty)))))



--
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
