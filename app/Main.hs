module Main where

import Semilattice
import Data.Map as M
import Data.Maybe
import Data.String

type SkuId = String
type Qty = Int
newtype LPN = LPN String deriving (Eq, Ord, Show)

instance IsString LPN where
    fromString = LPN

type LogicalDTId = String
type BagId = Int
type ShipmentId = String
type VanId = String
type FrameId = String
type PositionInFrame = Int
type PositionInVan = Int
type PositionInShipment = Int
type PositionInDT = Int

-- bounded join semilattices - objects
type Bag = Map SkuId (Increasing Qty)

type DT = Map PositionInDT Bag

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
pick pishipment pivan piframe dtlpn pidt skuId qty = base (pishipment, (bottom, base (pivan, (bottom, base (piframe, (Unambiguous dtlpn, base (pidt, base (skuId, Increasing qty))))))))

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

pickGoal :: PositionInShipment -> PositionInVan -> PositionInFrame -> PositionInDT -> SkuId -> Qty -> ShipmentGoal
pickGoal pishipment pivan piframe pidt skuId qty = base (pishipment, base (pivan, base (piframe, base (pidt, base (skuId, Increasing qty)))))

main :: IO ()
main = do
    let actual = shipmentToGoal $ bjsconcat [pick 0 0 1 "123" 0 "apple" 3, pick 0 0 1 "123" 1 "banana" 4, pick 0 0 1 "123" 0 "coconut" 1, pick 0 0 1 "123" 0 "coconut" 2, pick 0 0 1 "123" 2 "donut" 5, pick 0 0 1  "123" 2 "donut" 5, pick 0 0 2 "444" 0 "cucumber" 7]
    let expected = bjsconcat [pickGoal 0 0 1 0 "apple" 3, pickGoal 0 0 1 1 "banana" 4, pickGoal 0 0 1 0 "coconut" 2, pickGoal 0 0 1 2 "donut" 5, pickGoal 0 0 2 0 "cucumber" 7]
    print $ actual <+> expected -- True
    print $ actual +> expected -- True
    print $ actual <+ expected -- True


--
bag :: SkuId -> Qty -> Bag
bag skuId qty = base (skuId, Increasing qty)

bagToDT :: Int -> Bag -> DT
bagToDT pidt b = base (pidt, b)

dtToPhysicalState :: LPN -> DT -> PhysicalState
dtToPhysicalState lpn dt = (bottom, base (lpn, dt))

physicalToLogicalState :: PhysicalState -> LogicalState
physicalToLogicalState (assignments, p) = (\slpn -> case slpn of
    Unknown -> bottom
    Ambiguous _ -> bottom 
    Unambiguous lpn -> fromMaybe bottom (M.lookup lpn p)) <$> assignments
-- this is not homorphism, it's merely monotonic

dtAssignment :: LogicalDTId -> LPN -> DTAssignment
dtAssignment dtid lpn = base (dtid, Unambiguous lpn)

dtAssignmentToPhysicalState :: DTAssignment -> PhysicalState
dtAssignmentToPhysicalState a = (a, bottom)

--
-- main :: IO ()
-- main = do
--     let actual = bjsconcat [dtAssignment' "1" "123", physicalPick "123" 0 "apple" 3, physicalPick "123" 1 "banana" 4, physicalPick "123" 0 "coconut" 1, physicalPick "123" 0 "coconut" 2, physicalPick "123" 2 "donut" 5, physicalPick "123" 2 "donut" 5, dtAssignment' "2" "444", physicalPick "444" 0 "cucumber" 7]
--     let expected = bjsconcat [logicalPick "1" 0 "apple" 3, logicalPick "1" 1 "banana" 4]
--     print $ actual +> expected -- True
--     print $ actual <+ expected -- False 
--         where
--             physicalPick :: LPN -> BagId -> SkuId -> Qty -> LogicalState
--             physicalPick lpn bagId skuId = physicalToLogicalState . dtToPhysicalState lpn . bagToDT bagId . bag skuId
--             logicalPick :: LogicalDTId -> BagId -> SkuId -> Qty -> LogicalState
--             logicalPick dtId bagId skuId = physicalToLogicalState . dtToPhysicalState dtId . bagToDT bagId . bag skuId
--             dtAssignment' :: LogicalDTId -> LPN -> LogicalState
--             dtAssignment' dtid = physicalToLogicalState . dtAssignmentToPhysicalState . dtAssignment dtid
