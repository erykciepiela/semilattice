module Main where

import Semilattice
import Data.Map as M
import Data.Maybe
import Data.String
import Control.Monad
import Data.List as L

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

-- homomorphisms - morphisms
bag :: SkuId -> Qty -> Bag
bag skuId qty = base (skuId, Increasing qty)

dt :: Int -> Bag -> DT
dt pidt b = base (pidt, b)

picked :: PositionInShipment -> PositionInVan -> PositionInFrame -> LPN -> Int -> SkuId -> Qty -> Shipment
picked pishipment pivan piframe dtlpn pidt skuId qty = base (pishipment, (bottom, base (pivan, (bottom, base (piframe, (Unambiguous dtlpn, base (pidt, base (skuId, Increasing qty))))))))

frameLoaded :: PositionInShipment -> PositionInVan -> LPN -> Shipment
frameLoaded pishipment pivan frameLpn = base (pishipment, (bottom, base (pivan, (Unambiguous frameLpn, bottom))))

vanLoaded :: PositionInShipment -> LPN -> Shipment
vanLoaded pishipment vanLpn = base (pishipment, (Unambiguous vanLpn, bottom))

frameToGoal :: Frame -> FrameGoal
frameToGoal = fmap snd

vanToGoal :: Van -> VanGoal
vanToGoal = fmap $ frameToGoal . snd

pickedShipment :: Shipment -> ShipmentGoal
pickedShipment = fmap $ vanToGoal . snd

pickGoal :: PositionInShipment -> PositionInVan -> PositionInFrame -> PositionInDT -> SkuId -> Qty -> ShipmentGoal
pickGoal pishipment pivan piframe pidt skuId qty = base (pishipment, base (pivan, base (piframe, base (pidt, base (skuId, Increasing qty)))))

-- is this homomorphism?
frameloadedVan :: Van -> VanGoal 
frameloadedVan = fmap $ \(slpn, f) -> case slpn of Unknown -> bottom; Unambiguous _ -> frameToGoal f; Ambiguous _ -> bottom;

frameloadedShipment :: Shipment -> ShipmentGoal
frameloadedShipment = fmap $ frameloadedVan . snd

-- is this homomorphism?
vanloadedShipment :: Shipment -> ShipmentGoal
vanloadedShipment = fmap $ \(slpn, g) -> case slpn of Unknown -> bottom; Unambiguous _ -> vanToGoal g; Ambiguous _ -> bottom;

--
permuteDuplicates :: Int -> [[a]] -> [[a]]
permuteDuplicates duplicates as = L.permutations $ duplicate duplicates $ mconcat as
    where
        duplicate :: Int -> [a] -> [a]
        duplicate n as = mconcat $ replicate n as

main :: IO ()
main = do
    let pickZoneEvents = 
            [
                picked 0 0 0 "DT1" 0 "apple" 3, 
                picked 0 0 0 "DT1" 1 "banana" 4,
                picked 0 0 0 "DT1" 0 "coconut" 1,
                picked 0 0 0 "DT1" 0 "coconut" 2,
                picked 0 0 0 "DT1" 2 "donut" 5,
                picked 0 0 1 "DT2" 0 "cucumber" 7
            ]
    let frameLoadZoneEvents = 
            [
                frameLoaded 0 0 "F1"
            ]
    let vanLoadZoneEvents = 
            [
                vanLoaded 0 "V1"
            ]
    let expected = fromList [(0,("V1",fromList [(0,("F1",fromList [(0,("DT1",fromList [(0,fromList [("apple", 3),("coconut", 2)]),(1,fromList [("banana", 4)]),(2,fromList [("donut", 5)])])),(1,("DT2",fromList [(0,fromList [("cucumber", 7)])]))]))]))]
    let receivedEventsPermutations = L.take 10000 $ permuteDuplicates 4 [vanLoadZoneEvents, frameLoadZoneEvents, pickZoneEvents]
    print $ all (`ascendsTo` expected) receivedEventsPermutations
