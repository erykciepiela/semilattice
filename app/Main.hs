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
bag skuId qty = jirelement (skuId, Increasing qty)

dt :: Int -> Bag -> DT
dt pidt b = jirelement (pidt, b)

picked :: PositionInShipment -> PositionInVan -> PositionInFrame -> LPN -> Int -> SkuId -> Qty -> Shipment
picked pishipment pivan piframe dtlpn pidt skuId qty = jirelement (pishipment, (bottom, jirelement (pivan, (bottom, jirelement (piframe, (Unambiguous dtlpn, jirelement (pidt, jirelement (skuId, Increasing qty))))))))

frameLoaded :: PositionInShipment -> PositionInVan -> LPN -> Shipment
frameLoaded pishipment pivan frameLpn = jirelement (pishipment, (bottom, jirelement (pivan, (Unambiguous frameLpn, bottom))))

vanLoaded :: PositionInShipment -> LPN -> Shipment
vanLoaded pishipment vanLpn = jirelement (pishipment, (Unambiguous vanLpn, bottom))

frameToGoal :: Frame -> FrameGoal
frameToGoal = fmap snd

vanToGoal :: Van -> VanGoal
vanToGoal = fmap $ frameToGoal . snd

pickedShipment :: Shipment -> ShipmentGoal
pickedShipment = fmap $ vanToGoal . snd

pickGoal :: PositionInShipment -> PositionInVan -> PositionInFrame -> PositionInDT -> SkuId -> Qty -> ShipmentGoal
pickGoal pishipment pivan piframe pidt skuId qty = jirelement (pishipment, jirelement (pivan, jirelement (piframe, jirelement (pidt, jirelement (skuId, Increasing qty)))))

-- is this homomorphism?
frameloadedVan :: Van -> VanGoal 
frameloadedVan = fmap $ \(slpn, f) -> case slpn of Unknown -> bottom; Unambiguous _ -> frameToGoal f; Ambiguous _ -> bottom;

frameloadedShipment :: Shipment -> ShipmentGoal
frameloadedShipment = fmap $ frameloadedVan . snd

-- is this homomorphism?
vanloadedShipment :: Shipment -> ShipmentGoal
vanloadedShipment = fmap $ \(slpn, g) -> case slpn of Unknown -> bottom; Unambiguous _ -> vanToGoal g; Ambiguous _ -> bottom;

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
    print $ test 10000 4 expected $ mconcat [vanLoadZoneEvents, frameLoadZoneEvents, pickZoneEvents] -- True
    print $ bjsconcat $ vanloadedShipment <$> mconcat [vanLoadZoneEvents, frameLoadZoneEvents, pickZoneEvents] -- True
    print $ vanloadedShipment $ bjsconcat $ mconcat [vanLoadZoneEvents, frameLoadZoneEvents, pickZoneEvents] -- True
    -- print $ test 10000 4 expected $ vanloadedShipment <$> mconcat [vanLoadZoneEvents, frameLoadZoneEvents, pickZoneEvents] -- True

--
-- --- new b --   old b
-- f (a1 \/ a2) = f a1 \/ f a2 -- we only need last arrived a2, perform f against only a2, and merge with f a2
-- otherwise we need bjsconcat of all as, perform f against as

