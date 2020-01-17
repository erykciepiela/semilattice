module Main where

import Prelude hiding ((.), id)
import Control.Category
import Control.Monad
import Semilattice
import Data.String
import Data.List as L
import Data.Map as M
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
batchPicked pishipment pivan piframe pidt skuId st qty = jirelement (pishipment, (bottom, jirelement (pivan, (bottom, jirelement (piframe, (bottom, jirelement (pidt, jirelement (skuId, jirelement (st, jirelement qty)))))))))

dtManufactured :: PositionInShipment -> PositionInVan -> PositionInFrame -> LPN -> Shipment
dtManufactured pishipment pivan piframe dtlpn = jirelement (pishipment, (bottom, jirelement (pivan, (bottom, jirelement (piframe, (jirelement dtlpn, bottom))))))

frameLoaded :: PositionInShipment -> PositionInVan -> LPN -> Shipment
frameLoaded pishipment pivan frameLpn = jirelement (pishipment, (bottom, jirelement (pivan, (jirelement frameLpn, bottom))))

vanLoaded :: PositionInShipment -> LPN -> Shipment
vanLoaded pishipment vanLpn = jirelement (pishipment, (jirelement vanLpn, bottom))

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
-- | Returns list of possible list of groups of elements
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
                batchPicked 0 0 0 0 "apple" 0 3, 
                batchPicked 0 0 0 1 "banana" 1 2,
                batchPicked 0 0 0 1 "banana" 1 4,
                batchPicked 0 0 0 0 "coconut" 2 1,
                batchPicked 0 0 0 0 "coconut" 3 1,
                batchPicked 0 0 0 2 "donut" 4 5,
                batchPicked 0 0 1 0 "cucumber" 5 7,
                dtManufactured 0 0 0 "DT1",
                dtManufactured 0 0 1 "DT2",
                frameLoaded 0 0 "F1",
                vanLoaded 0 "V1"
            ]
    let expectedState = GrowingMap {growingMap = fromList [(0,(Unambiguous "V1",GrowingMap {growingMap = fromList [(0,(Unambiguous "F1",GrowingMap {growingMap = fromList [(0,(Unambiguous "DT1",GrowingMap {growingMap = fromList [(0,GrowingMap {growingMap = fromList [("apple",GrowingMap {growingMap = fromList [(0,Increasing {increasing = 3})]}),("coconut",GrowingMap {growingMap = fromList [(2,Increasing {increasing = 1}),(3,Increasing {increasing = 1})]})]}),(1,GrowingMap {growingMap = fromList [("banana",GrowingMap {growingMap = fromList [(1,Increasing {increasing = 4})]})]}),(2,GrowingMap {growingMap = fromList [("donut",GrowingMap {growingMap = fromList [(4,Increasing {increasing = 5})]})]})]})),(1,(Unambiguous "DT2",GrowingMap {growingMap = fromList [(0,GrowingMap {growingMap = fromList [("cucumber",GrowingMap {growingMap = fromList [(5,Increasing {increasing = 7})]})]})]}))]}))]}))]}
    print $ all (`isEventuallyConsistent` expectedState) (L.take 100000 (messedUp events))  -- True
