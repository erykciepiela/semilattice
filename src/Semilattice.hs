module Semilattice where

-- | <> denotes "merging" knowledge
-- | commutativity saves us from out of order messages problem
-- | idempotence saves us from exactly-once delivery guarantee problem
class (Eq s, Monoid s) => Semilattice s where
    -- a <> b = b <> a - commutativity
    -- a <> a = a - idempotence

isAchieved :: Semilattice s => s -> s -> Bool
isAchieved goal s = s <> goal == s

isAchieved' :: Semilattice s => s -> [s] -> Bool
isAchieved' goal ss = isAchieved goal (mconcat ss)

areAchieved' :: Semilattice s => [s] -> [s] -> Bool
areAchieved' goals ss = isAchieved (mconcat goals) (mconcat ss)
