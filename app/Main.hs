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

-- functions(Same LPN, 
foo :: Frame -> Map LPN PositionInFrame
foo = undefined

-- homomorphisms - morphisms
bag :: SkuId -> Qty -> Bag
bag skuId qty = base (skuId, Increasing qty)

dt :: Int -> Bag -> DT
dt pidt b = base (pidt, b)

pick :: PositionInShipment -> PositionInVan -> PositionInFrame -> LPN -> Int -> SkuId -> Qty -> Shipment
pick pishipment pivan piframe dtlpn pidt skuId qty = base (pishipment, (bottom, base (pivan, (bottom, base (piframe, (Unambiguous dtlpn, base (pidt, base (skuId, Increasing qty))))))))

frameLoad :: PositionInShipment -> PositionInVan -> LPN -> Shipment
frameLoad pishipment pivan frameLpn = base (pishipment, (bottom, base (pivan, (Unambiguous frameLpn, bottom))))

vanLoad :: PositionInShipment -> LPN -> Shipment
vanLoad pishipment vanLpn = base (pishipment, (Unambiguous vanLpn, bottom))

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

main :: IO ()
main = do
    let actual = bjsconcat [pick 0 0 1 "123" 0 "apple" 3, pick 0 0 1 "123" 1 "banana" 4, pick 0 0 1 "123" 0 "coconut" 1, pick 0 0 1 "123" 0 "coconut" 2, pick 0 0 1 "123" 2 "donut" 5, pick 0 0 1  "123" 2 "donut" 5, pick 0 0 2 "444" 0 "cucumber" 7, frameLoad 0 0 "f1", vanLoad 0 "v1"]
    let expected = bjsconcat [pickGoal 0 0 1 0 "apple" 3, pickGoal 0 0 1 1 "banana" 4, pickGoal 0 0 1 0 "coconut" 2, pickGoal 0 0 1 2 "donut" 5, pickGoal 0 0 2 0 "cucumber" 7]
    let actuallyPicked = pickedShipment actual
    let actuallyFrameloaded = frameloadedShipment actual
    let actuallyVanloaded = vanloadedShipment actual
    print $ actuallyPicked <+> expected -- True
    print $ actuallyPicked +> expected -- True
    print $ actuallyPicked <+ expected -- True
    print $ actuallyFrameloaded <+> expected -- True
    print $ actuallyFrameloaded +> expected -- True
    print $ actuallyFrameloaded <+ expected -- True
    print $ actuallyVanloaded <+> expected -- True
    print $ actuallyVanloaded +> expected -- True
    print $ actuallyVanloaded <+ expected -- True
    print actuallyFrameloaded
    print actuallyVanloaded
