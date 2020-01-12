module Main where

import Prelude hiding ((.), id)
import Semilattice
import Data.Maybe
import Data.String
import Control.Monad
import Control.Category
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
type PositionInDT = Int
type PositionInFrame = Int
type PositionInVan = Int
type PositionInShipment = Int

-- bounded join semilattices - objects
type Bag = GrowingMap SkuId (Increasing Qty)

type DT = GrowingMap PositionInDT Bag

type Frame = GrowingMap PositionInFrame (Same LPN, DT)

type Van = GrowingMap PositionInVan (Same LPN, Frame)

type Shipment = GrowingMap PositionInShipment (Same LPN, Van)

type FrameGoal = GrowingMap PositionInFrame DT

type VanGoal = GrowingMap PositionInVan FrameGoal

type ShipmentGoal = GrowingMap PositionInShipment VanGoal

-- homomorphisms - morphisms
bag :: SkuId -> Qty -> Bag
bag skuId qty = jirelement (skuId, Increasing qty)

dt :: Int -> Bag -> DT
dt pidt b = jirelement (pidt, b)

bagPicked :: PositionInShipment -> PositionInVan -> PositionInFrame -> PositionInDT -> SkuId -> Qty -> Shipment
bagPicked pishipment pivan piframe pidt skuId qty = jirelement (pishipment, (bottom, jirelement (pivan, (bottom, jirelement (piframe, jirelement (Right (pidt, jirelement (skuId, jirelement qty))))))))

dtPicked :: PositionInShipment -> PositionInVan -> PositionInFrame -> LPN -> Shipment
dtPicked pishipment pivan piframe dtlpn = jirelement (pishipment, (bottom, jirelement (pivan, (bottom, jirelement (piframe, jirelement (Left dtlpn))))))

frameLoaded :: PositionInShipment -> PositionInVan -> LPN -> Shipment
frameLoaded pishipment pivan frameLpn = jirelement (pishipment, (bottom, jirelement (pivan, jirelement (Left frameLpn))))

vanLoaded :: PositionInShipment -> LPN -> Shipment
vanLoaded pishipment vanLpn = jirelement (pishipment, jirelement (Left vanLpn))

frameToGoal :: Homo Frame FrameGoal
frameToGoal = propagateMap propagateSnd

vanToGoal :: Homo Van VanGoal
vanToGoal = propagateMap $ frameToGoal . propagateSnd

pickedShipment :: Homo Shipment ShipmentGoal
pickedShipment = propagateMap $ vanToGoal . propagateSnd

pickGoal :: PositionInShipment -> PositionInVan -> PositionInFrame -> PositionInDT -> SkuId -> Qty -> ShipmentGoal
pickGoal pishipment pivan piframe pidt skuId qty = jirelement (pishipment, jirelement (pivan, jirelement (piframe, jirelement (pidt, jirelement (skuId, Increasing qty)))))

-- is this homomorphism?
-- frameloadedVan :: Van -> VanGoal 
-- frameloadedVan = propagateMap $ \(slpn, f) -> case slpn of Unknown -> bottom; Unambiguous _ -> frameToGoal f; Ambiguous _ -> bottom;

-- frameloadedShipment :: Shipment -> ShipmentGoal
-- frameloadedShipment = propagateMap $ frameloadedVan . snd

-- is this homomorphism?
-- vanloadedShipment :: Shipment -> ShipmentGoal
-- vanloadedShipment = propagateMap $ \(slpn, g) -> case slpn of Unknown -> bottom; Unambiguous _ -> vanToGoal g; Ambiguous _ -> bottom;

--

test :: (Eq a, BoundedJoinSemilattice a) => Int -> Int -> a -> [a] -> Bool
test permNo dupNo final as = all (`ascendsTo` final) $ L.take permNo $ permuteDuplicates dupNo as
    where
        permuteDuplicates :: Int -> [a] -> [[a]]
        permuteDuplicates duplicates as = L.permutations $ duplicate duplicates as
            where
                duplicate :: Int -> [a] -> [a]
                duplicate n as = mconcat $ replicate n as

main :: IO ()
main = do
    let pickZoneEvents = 
            [
                bagPicked 0 0 0 0 "apple" 3, 
                bagPicked 0 0 0 1 "banana" 4,
                bagPicked 0 0 0 0 "coconut" 1,
                bagPicked 0 0 0 0 "coconut" 2,
                bagPicked 0 0 0 2 "donut" 5,
                bagPicked 0 0 1 0 "cucumber" 7,
                dtPicked 0 0 0 "DT1",
                dtPicked 0 0 1 "DT2"
            ]
    let frameLoadZoneEvents = 
            [
                frameLoaded 0 0 "F1"
            ]
    let vanLoadZoneEvents = 
            [
                vanLoaded 0 "V1"
            ]
    let expected = bconcat [(0,("V1",bconcat [(0,("F1",bconcat [(0,("DT1",bconcat [(0,bconcat [("apple", 3),("coconut", 2)]),(1,bconcat [("banana", 4)]),(2,bconcat [("donut", 5)])])),(1,("DT2",bconcat [(0,bconcat [("cucumber", 7)])]))]))]))]
    print $ test 10000 4 expected $ mconcat [vanLoadZoneEvents, frameLoadZoneEvents, pickZoneEvents] -- True
    let expected' = bag "apple" 3 \/ bag "coconut" 2
    print $ test 10000 4 expected' $ homo (propagateBag 0 0 0 0) <$> mconcat [vanLoadZoneEvents, frameLoadZoneEvents, pickZoneEvents] -- True

propagateBag :: PositionInShipment -> PositionInVan -> PositionInFrame -> PositionInDT -> Homo Shipment Bag
propagateBag piShipment piVan piFrame piDT = propagateMapEntry piDT . propagateSnd . propagateMapEntry piFrame . propagateSnd . propagateMapEntry piVan . propagateSnd . propagateMapEntry piShipment 

--
-- --- new b --   old b
-- f (a1 \/ a2) = f a1 \/ f a2 -- we only need last arrived a2, perform f against only a2, and merge with f a2
-- otherwise we need bjsconcat of all as, perform f against as

