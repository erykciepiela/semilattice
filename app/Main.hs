module Main where

import Prelude hiding ((.), id)
import Control.Category
import Control.Monad
import Semilattice
import Data.String
import Data.List as L
import Data.Map as M
import qualified Data.Set as S
import Debug.Trace

-- domain types
type SKU = Int
type Qty = Int
type LPN = Int
type PositionInDT = Int
type PositionInFrame = Int
type PositionInVan = Int
type PositionInShipment = Int
type ST = Int

-- bounded join semilattices
type Batch = Map ST (Increasing Qty)

type Bag = Map SKU Batch

type DT = Map PositionInDT Bag

type Frame = Map PositionInFrame (Same LPN, DT)

type Van = Map PositionInVan (Same LPN, Frame)

type Shipment = Map PositionInShipment (Same LPN, Van)

-- | ShipmentEvent is dual to Shipment i.e. every Shipment can be build with a number of ShipmentEvents joined, also every Shipment can be split into number of ShipmentEvents
type ShipmentEvent = (PositionInShipment, Either LPN (PositionInVan, Either LPN (PositionInFrame, Either LPN (PositionInDT, (SKU, (ST, Qty))))))

-- | ShipmentEvent constructors
picked :: PositionInShipment -> PositionInVan -> PositionInFrame -> PositionInDT -> SKU -> ST -> Qty -> ShipmentEvent
picked pishipment pivan piframe pidt skuId st qty = (pishipment, Right (pivan, Right (piframe, Right (pidt, (skuId, (st, qty))))))

dtManufactured :: PositionInShipment -> PositionInVan -> PositionInFrame -> LPN -> ShipmentEvent
dtManufactured pishipment pivan piframe dtlpn = (pishipment, Right (pivan, Right (piframe, Left dtlpn)))

frameManufactured :: PositionInShipment -> PositionInVan -> LPN -> ShipmentEvent
frameManufactured pishipment pivan frameLpn = (pishipment, Right (pivan, Left frameLpn))

vanManufactured :: PositionInShipment -> LPN -> ShipmentEvent
vanManufactured pishipment vanLpn = (pishipment, Left vanLpn)

-- | Shipment homomorphisms
shipmentVan :: PositionInShipment -> Homo Shipment Van
shipmentVan piShipment = propagateSnd . propagateMapEntry piShipment 

shipmentFrame :: PositionInShipment -> PositionInVan -> Homo Shipment Frame
shipmentFrame piShipment piVan = propagateSnd . propagateMapEntry piVan . shipmentVan piShipment 

shipmentDT :: PositionInShipment -> PositionInVan -> PositionInFrame -> Homo Shipment DT
shipmentDT piShipment piVan piFrame = propagateSnd . propagateMapEntry piFrame . shipmentFrame piShipment piVan

shipmentDTLPN :: PositionInShipment -> PositionInVan -> PositionInFrame -> Homo Shipment (Same LPN)
shipmentDTLPN piShipment piVan piFrame = propagateFst . propagateMapEntry piFrame . shipmentFrame piShipment piVan

shipmentBag :: PositionInShipment -> PositionInVan -> PositionInFrame -> PositionInDT -> Homo Shipment Bag
shipmentBag piShipment piVan piFrame piDT = propagateMapEntry piDT . shipmentDT piShipment piVan piFrame

shipmentPositionsDone :: Homo Shipment (S.Set PositionInShipment)
shipmentPositionsDone = propagateMapKeys 

-- | Messes up original list by doubling each element, permuting elements and grouping subsequences of elements.
-- | Returns list of messed up list of groups (lists) of elements
messedUp :: [a] -> [[[a]]]
messedUp originalList = mconcat $ groupings <$> L.permutations (duplicates originalList)
    where
    groupings :: [a] -> [[[a]]]
    groupings [a] = [[[a]]]
    groupings as =  mconcat $ ((\(i :: [a], t :: [a]) -> ([i] <>) <$> groupings t) <$> zip (init $ tail $ inits as) (init $ tail $ tails as)) <> [[[as]]]
    duplicates :: [a] -> [a]
    duplicates as = mconcat $ replicate 2 as

main :: IO ()
main = do
    -- number of possible messed up lists for n events
    -- print $ length $ messedUp [1..1] -- for 1 event it's 4
    -- print $ length $ messedUp [1..2] -- for 2 event it's = 192
    -- print $ length $ messedUp [1..3] -- for 3 event it's > 23k
    -- print $ length $ messedUp [1..4] -- for 4 event it's > 5M
    let shipmentEvents = 
            [
                picked 0 0 0 0 1 0 3,  -- 3 apples moved from ST 0 to bag 0 in dt 0 in frame 0 in van 0
                picked 0 0 0 1 2 1 2, -- 2 bananas moved from ST 1 to bag 0 in dt 0 in frame 0 in van 0, actually it was...
                picked 0 0 0 1 2 1 4, -- 4 bananas moved from ST 1 to bag 0 in dt 0 in frame 0 in van 0, and it's ok as long as 4 >= 2
                picked 0 0 0 0 3 2 1,-- 1 3 moved from ST 2 to bag 0 in dt 0 in frame 0 in van 0, but it's too few, and there's no more cocunuts in ST 2, so...
                picked 0 0 0 0 3 3 1,-- 1 3 moved from ST 3 to bag 0 in dt 0 in frame 0 in van 0, but it's too few, we need more...
                picked 0 0 0 2 4 4 5,  -- 5 donuts moved from ST 4 to bag 2 in dt 0 in frame 0 in van 0, and from the same ST but to different DT...
                picked 0 0 1 0 4 4 7,  -- 7 donuts moved from ST 4 to bag 0 in dt 1 in frame 0 in van 0
                dtManufactured 0 0 0 1,  -- dt 0 in frame 0 in van 0 has been picket totally and it has LPN DT1
                dtManufactured 0 0 1 2,  -- dt 1 in frame 0 in van 0 has been picket totally and it has LPN DT2
                frameManufactured 0 0 1,  -- frame 0 in van 0 has been loaded and it has LPN F1
                vanManufactured 0 1       -- 0 has been loaded and it has LPN V1
            ]
    let shipmentShipment = fromList [(0,(Unambiguous 1,fromList [(0,(Unambiguous 1,fromList [(0,(Unambiguous 1,fromList [(0,fromList [(1,fromList [(0,Increasing {increasing = 3})]),(3,fromList [(2,Increasing {increasing = 1}),(3,Increasing {increasing = 1})])]),(1,fromList [(2,fromList [(1,Increasing {increasing = 4})])]),(2,fromList [(4,fromList [(4,Increasing {increasing = 5})])])])),(1,(Unambiguous 2,fromList [(0,fromList [(4,fromList [(4,Increasing {increasing = 7})])])]))]))]))]
    print $ all (\es -> (fmap jirelement <$> es) `isEventuallyConsistent` shipmentShipment) (L.take 100000 (messedUp shipmentEvents))  -- True
    print $ (`propagatedHomo` (prop . composeHomo)) (collect shipmentEvents) `ascendsTowards` S.fromList [1, 3] -- True
    print $ decompose shipmentShipment 
    
    -- print $ all (`isEventuallyConsistent` (S.Set {growingSet = S.fromList ["1","3"]})) ((propagateHomo prop . fmap (fmap bjsconcat) <$> (L.take 100000 (messedUp shipmentEvents))))

-- what SKUs are in given bag
prop :: Homo Shipment (S.Set SKU)
prop = propagateMapKeys . propagateMapEntry 0 . propagateSnd . propagateMapEntry 0 . propagateSnd . propagateMapEntry 0 . propagateSnd . propagateMapEntry 0
