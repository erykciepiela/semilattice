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
type SKU = String
type Qty = Int
type LPN = String
type PositionInDT = Int
type PositionInFrame = Int
type PositionInVan = Int
type PositionInShipment = Int
type ST = Int

-- bounded join semilattices
type Batch = GrowingMap ST (Increasing Qty)

type Bag = GrowingMap SKU Batch

type DT = GrowingMap PositionInDT Bag

type Frame = GrowingMap PositionInFrame (Same LPN, DT)

type Van = GrowingMap PositionInVan (Same LPN, Frame)

type Shipment = GrowingMap PositionInShipment (Same LPN, Van)

-- join-irreducible elements
batchPicked :: PositionInShipment -> PositionInVan -> PositionInFrame -> PositionInDT -> SKU -> ST -> Qty -> Shipment
batchPicked pishipment pivan piframe pidt skuId st qty = jirelement (pishipment, Right (pivan, Right (piframe, Right (pidt, (skuId, (st, qty))))))

dtManufactured :: PositionInShipment -> PositionInVan -> PositionInFrame -> LPN -> Shipment
dtManufactured pishipment pivan piframe dtlpn = jirelement (pishipment, Right (pivan, Right (piframe, Left dtlpn)))

frameManufactured :: PositionInShipment -> PositionInVan -> LPN -> Shipment
frameManufactured pishipment pivan frameLpn = jirelement (pishipment, Right (pivan, Left frameLpn))

vanManufactured :: PositionInShipment -> LPN -> Shipment
vanManufactured pishipment vanLpn = jirelement (pishipment, Left vanLpn)

-- homomorphisms
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

shipmentPositionsDone :: Homo Shipment (GrowingSet PositionInShipment)
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
    print $ length $ messedUp [1..1] -- for 1 event it's 4
    print $ length $ messedUp [1..2] -- for 2 event it's = 192
    print $ length $ messedUp [1..3] -- for 3 event it's > 23k
    print $ length $ messedUp [1..4] -- for 4 event it's > 5M
    let events = 
            [
                batchPicked 0 0 0 0 "apple" 0 3,  -- 3 apples moved from ST 0 to bag 0 in dt 0 in frame 0 in van 0
                batchPicked 0 0 0 1 "banana" 1 2, -- 2 bananas moved from ST 1 to bag 0 in dt 0 in frame 0 in van 0, actually it was...
                batchPicked 0 0 0 1 "banana" 1 4, -- 4 bananas moved from ST 1 to bag 0 in dt 0 in frame 0 in van 0, and it's ok as long as 4 >= 2
                batchPicked 0 0 0 0 "coconut" 2 1,-- 1 coconut moved from ST 2 to bag 0 in dt 0 in frame 0 in van 0, but it's too few, and there's no more cocunuts in ST 2, so...
                batchPicked 0 0 0 0 "coconut" 3 1,-- 1 coconut moved from ST 3 to bag 0 in dt 0 in frame 0 in van 0, but it's too few, we need more...
                batchPicked 0 0 0 2 "donut" 4 5,  -- 5 donuts moved from ST 4 to bag 2 in dt 0 in frame 0 in van 0, and from the same ST but to different DT...
                batchPicked 0 0 1 0 "donut" 4 7,  -- 7 donuts moved from ST 4 to bag 0 in dt 1 in frame 0 in van 0
                dtManufactured 0 0 0 "DT1",       -- dt 0 in frame 0 in van 0 has been picket totally and it has LPN DT1
                dtManufactured 0 0 1 "DT2",       -- dt 1 in frame 0 in van 0 has been picket totally and it has LPN DT2
                frameManufactured 0 0 "F1",       -- frame 0 in van 0 has been loaded and it has LPN F1
                vanManufactured 0 "V1"            -- 0 has been loaded and it has LPN V1
            ]
    let expectedState = GrowingMap {growingMap = fromList [(0,(Unambiguous "V1",GrowingMap {growingMap = fromList [(0,(Unambiguous "F1",GrowingMap {growingMap = fromList [(0,(Unambiguous "DT1",GrowingMap {growingMap = fromList [(0,GrowingMap {growingMap = fromList [("apple",GrowingMap {growingMap = fromList [(0,Increasing {increasing = 3})]}),("coconut",GrowingMap {growingMap = fromList [(2,Increasing {increasing = 1}),(3,Increasing {increasing = 1})]})]}),(1,GrowingMap {growingMap = fromList [("banana",GrowingMap {growingMap = fromList [(1,Increasing {increasing = 4})]})]}),(2,GrowingMap {growingMap = fromList [("donut",GrowingMap {growingMap = fromList [(4,Increasing {increasing = 5})]})]})]})),(1,(Unambiguous "DT2",GrowingMap {growingMap = fromList [(0,GrowingMap {growingMap = fromList [("donut",GrowingMap {growingMap = fromList [(4,Increasing {increasing = 7})]})]})]}))]}))]}))]}
    print $ all (`isEventuallyConsistent` expectedState) (L.take 100000 (messedUp events))  -- True
    print $ (`propagatedHomo` prop) events `ascendsTowards` (GrowingSet {growingSet = S.fromList ["apple","coconut"]})
    -- print $ all (`isEventuallyConsistent` (GrowingSet {growingSet = S.fromList ["apple","coconut"]})) ((propagateHomo prop . fmap (fmap bjsconcat) <$> (L.take 100000 (messedUp events))))

-- what SKUs are in given bag
prop :: Homo Shipment (GrowingSet SKU)
prop = propagateMapKeys . propagateMapEntry 0 . propagateSnd . propagateMapEntry 0 . propagateSnd . propagateMapEntry 0 . propagateSnd . propagateMapEntry 0
