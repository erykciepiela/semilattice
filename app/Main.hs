module Main where

import Prelude hiding ((.), id)
import Control.Category
import Semilattice
import Data.String
import Data.List as L
-- import Data.Set as S
import Data.Map as M

type SkuId = String
type Qty = Int
newtype LPN = LPN String deriving (Eq, Ord, Show)

instance IsString LPN where
    fromString = LPN

type PositionInDT = Int
type PositionInFrame = Int
type PositionInVan = Int
type PositionInShipment = Int
type ST = Int

-- bounded join semilattices - objects
type Batch = GrowingMap ST (Increasing Qty)

type Bag = GrowingMap SkuId Batch

type DT = GrowingMap PositionInDT Bag

type Frame = GrowingMap PositionInFrame (Same LPN, DT)

type Van = GrowingMap PositionInVan (Same LPN, Frame)

type Shipment = GrowingMap PositionInShipment (Same LPN, Van)

-- join-irreducible elements
batch :: ST -> Qty -> Batch
batch st qty = jirelement (st, jirelement qty)

bag :: SkuId -> Batch -> Bag
bag skuId batch = jirelement (skuId, batch)

dt :: PositionInDT -> Bag -> DT
dt pidt bag = jirelement (pidt, bag)

bagPicked :: PositionInShipment -> PositionInVan -> PositionInFrame -> PositionInDT -> SkuId -> ST -> Qty -> Shipment
bagPicked pishipment pivan piframe pidt skuId st qty = jirelement (pishipment, (bottom, jirelement (pivan, (bottom, jirelement (piframe, (bottom, jirelement (pidt, jirelement (skuId, jirelement (st, jirelement qty)))))))))

dtPicked :: PositionInShipment -> PositionInVan -> PositionInFrame -> LPN -> Shipment
dtPicked pishipment pivan piframe dtlpn = jirelement (pishipment, (bottom, jirelement (pivan, (bottom, jirelement (piframe, (jirelement dtlpn, bottom))))))

frameLoaded :: PositionInShipment -> PositionInVan -> LPN -> Shipment
frameLoaded pishipment pivan frameLpn = jirelement (pishipment, (bottom, jirelement (pivan, (jirelement frameLpn, bottom))))

vanLoaded :: PositionInShipment -> LPN -> Shipment
vanLoaded pishipment vanLpn = jirelement (pishipment, (jirelement vanLpn, bottom))

-- homomorphisms - morphisms
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
                bagPicked 0 0 0 0 "apple" 0 3, 
                bagPicked 0 0 0 1 "banana" 1 4,
                bagPicked 0 0 0 0 "coconut" 2 1,
                bagPicked 0 0 0 0 "coconut" 3 1,
                bagPicked 0 0 0 2 "donut" 4 5,
                bagPicked 0 0 1 0 "cucumber" 5 7,
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
    let expected = GrowingMap {growingMap = fromList [(0,(Unambiguous (LPN "V1"),GrowingMap {growingMap = fromList [(0,(Unambiguous (LPN "F1"),GrowingMap {growingMap = fromList [(0,(Unambiguous (LPN "DT1"),GrowingMap {growingMap = fromList [(0,GrowingMap {growingMap = fromList [("apple",GrowingMap {growingMap = fromList [(0,Increasing {increasing = 3})]}),("coconut",GrowingMap {growingMap = fromList [(2,Increasing {increasing = 1}),(3,Increasing {increasing = 1})]})]}),(1,GrowingMap {growingMap = fromList [("banana",GrowingMap {growingMap = fromList [(1,Increasing {increasing = 4})]})]}),(2,GrowingMap {growingMap = fromList [("donut",GrowingMap {growingMap = fromList [(4,Increasing {increasing = 5})]})]})]})),(1,(Unambiguous (LPN "DT2"),GrowingMap {growingMap = fromList [(0,GrowingMap {growingMap = fromList [("cucumber",GrowingMap {growingMap = fromList [(5,Increasing {increasing = 7})]})]})]}))]}))]}))]}
    print $ test 10000 4 expected $ mconcat [vanLoadZoneEvents, frameLoadZoneEvents, pickZoneEvents] -- True
    
    -- let expected' = bag "apple" (batch 0 3) \/ bag "coconut" (batch 2 1) \/ bag "coconut" (batch 3 1)
    -- print $ test 10000 4 expected' $ homo (shipmentBag 0 0 0 0) <$> mconcat [vanLoadZoneEvents, frameLoadZoneEvents, pickZoneEvents] -- True
    -- print $ runProc (Proc (shipmentDTLPN 0 0 1) id) $ mconcat [vanLoadZoneEvents, frameLoadZoneEvents, pickZoneEvents] -- True
