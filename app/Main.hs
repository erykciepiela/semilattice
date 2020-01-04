module Main where

import qualified JoinSemilattice as S
import Data.Map as M
import Data.Map.Append
import Data.Semigroup
import Data.Maybe

type PickId = String
type SkuId = String
type Qty = Int
type Batch = (String, SkuId)
type DTId = String
type LPN = String

type Bag = S.Map Batch (S.Max Qty)

bag :: PickId -> SkuId -> Qty -> Bag
bag pickId skuId qty = S.map (pickId, skuId) (S.max qty)

bagContent :: Bag -> Map SkuId Qty
bagContent b = mapKeysWith (+) snd $ getMax <$> unAppendMap b

type Bag' = S.Map SkuId (S.Max Qty)

-- propagator
bagContent' :: Bag -> Bag'
bagContent' b = AppendMap $ mapKeysWith (\max1 max2 -> Max $ getMax max1 + getMax max2) snd $ unAppendMap b


type DT = (Bag, Bag, Bag)

dt :: Int -> Bag -> DT
dt 0 b = (b, mempty, mempty)
dt 1 b = (mempty, b, mempty)
dt 2 b = (mempty, mempty, b)

dtContent :: DT -> (Map SkuId Qty, Map SkuId Qty, Map SkuId Qty)
dtContent (b1, b2, b3) = (bagContent b1, bagContent b2, bagContent b3)

type DT' = (Bag', Bag', Bag')

-- propagator
dtContent' :: DT -> DT'
dtContent' (b1, b2, b3) = (bagContent' b1, bagContent' b2, bagContent' b3)

type State = (S.Map DTLogicalId (S.Value LPN), S.Map LPN DT)

picking :: LPN -> Int -> PickId -> SkuId -> Qty -> State
picking lpn bagId batchId skuId qty = picking' lpn $ dt bagId $ bag batchId skuId qty
    where
        picking' :: LPN -> DT -> State
        picking' lpn dt = (mempty, S.map lpn dt)

assigning :: DTLogicalId -> LPN -> State
assigning dtid lpn = (S.map dtid (S.Value lpn), mempty)

stateContent :: State -> Map DTLogicalId (S.Value (LPN, (Map SkuId Qty, Map SkuId Qty, Map SkuId Qty)))
stateContent (assignments, p) = (\plpn -> (\lpn -> (lpn, maybe (mempty, mempty, mempty) dtContent (M.lookup lpn (unAppendMap p)))) <$> plpn) <$> unAppendMap assignments -- dtContent <$> unAppendMap p

type State' = S.Map DTLogicalId (S.Value DT')

-- propagator
stateContent' :: State -> State'
stateContent' (assignments, p) = AppendMap $ (\plpn -> (\lpn -> maybe (mempty, mempty, mempty) dtContent' (M.lookup lpn (unAppendMap p))) <$> plpn) <$> unAppendMap assignments

data Pick = Pick LPN Int PickId SkuId Qty

type F = (S.Promise DTId, S.Promise DTId)

type DTLogicalId = String

main :: IO ()
main = print $ stateContent' $ mconcat [
    assigning "1" "123", 
    picking "123" 0 "1" "apple" 3, 
    picking "123" 1 "2" "banana" 4, 
    picking "123" 0 "3" "coconut" 1, 
    picking "123" 0 "4" "coconut" 2, 
    picking "123" 2 "5" "donut" 5, 
    picking "123" 2 "5" "donut" 5,
    assigning "2" "444",
    picking "444" 0 "6" "cucumber" 7
    ]
