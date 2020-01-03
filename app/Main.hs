module Main where

import qualified JoinSemilattice as S
import Data.Map
import Data.Map.Append
import Data.Semigroup

type PickId = String
type SkuId = String
type Qty = Int
type Batch = (String, SkuId)
type DTId = String
type LPN = String

type Bag = S.Map Batch (S.Max Qty)

bag :: PickId -> SkuId -> Qty -> Bag
bag pickId skuId qty = S.map (pickId, skuId) (S.max qty)
-- bag pickId skuId qty = S.from ((pickId, skuId), qty)

toBatch :: PickId -> SkuId -> Qty -> Bag
toBatch = bag

bagContent :: Bag -> Map SkuId Qty
bagContent b = mapKeysWith (+) snd $ getMax <$> unAppendMap b

type DT = (Bag, Bag, Bag)

dt :: Int -> Bag -> DT
dt 0 b = (b, mempty, mempty)
dt 1 b = (mempty, b, mempty)
dt 2 b = (mempty, mempty, b)

toBag :: Int -> Bag -> DT
toBag = dt

dtContent :: DT -> (Map SkuId Qty, Map SkuId Qty, Map SkuId Qty)
dtContent (b1, b2, b3) = (bagContent b1, bagContent b2, bagContent b3)

type Picking = S.Map LPN DT

picking :: LPN -> DT -> Picking
picking = S.map

toDt :: LPN -> DT -> Picking
toDt = picking

pickingContent :: Picking -> Map LPN (Map SkuId Qty, Map SkuId Qty, Map SkuId Qty)
pickingContent p = dtContent <$> unAppendMap p

data Pick = Pick LPN Int PickId SkuId Qty

foo :: Pick -> Picking
foo (Pick lpn bagId batchId skuId qty) = toDt lpn $ toBag bagId $ toBatch batchId skuId qty

type F = (S.Promise DTId, S.Promise DTId)

picking1 :: Pick
picking1 = Pick "123" 0 "1" "apple" 3

picking2 :: Pick
picking2 = Pick "123" 1 "2" "banana" 4

picking3 :: Pick
picking3 = Pick "123" 0 "3" "coconut" 1

picking4 :: Pick
picking4 = Pick "123" 0 "4" "coconut" 2

picking5 :: Pick
picking5 = Pick "123" 2 "5" "donut" 5

main :: IO ()
main = print $ pickingContent $ mconcat $ foo <$> [
    picking1, 
    picking2, 
    picking3, 
    picking4, 
    picking5, 
    picking5
    ]
