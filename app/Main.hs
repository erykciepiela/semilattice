module Main where

import JoinSemilattice as S

type PickId = String
type SkuId = String
type Qty = Int
type Batch = (String, SkuId)

type Bag = (S.Map Batch (S.Max Qty))

type DT = (Bag, Bag, Bag)

firstBag :: SemiLat DT Bag
firstBag = Homo (\(b, _, _) -> b)

secondBag :: SemiLat DT Bag
secondBag = Homo (\(_, b, _) -> b)

thirdBag :: SemiLat DT Bag
thirdBag = Homo (\(_, _, b) -> b)

type F = (DT, DT)



pick1 :: DT
pick1 = (S.map ("1", "apple") (S.max 3), mempty, mempty)

pick2 :: DT
pick2 = (mempty, S.map ("2", "banana") (S.max 4), mempty)

pick3 :: DT
pick3 = (S.map ("3", "coconut") (S.max 1), mempty, mempty)

pick4 :: DT
pick4 = (S.map ("3", "coconut") (S.max 2), mempty, mempty)

pick5 :: DT
pick5 = (mempty, mempty, S.map ("4", "donut") (S.max 5))

dt1 :: DT
dt1 = pick1 <> pick2 <> pick3 <> pick4 <> pick5

type DTContent = (S.Map SkuId (S.Max Qty))

foo :: SemiLat DT DTContent
foo = Homo dtContent
    where
        dtContent (bag1, bag2, bag3) = undefined 

main :: IO ()
main = do
    print dt1
