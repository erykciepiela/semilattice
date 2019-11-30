module Lib where

import Data.Time
import Data.Time.Format
import Data.Set

-- | <> denotes "merging" knowledge
-- | commutativity saves us from out of order messages problem
-- | idempotence saves us from exactly-once delivery guarantee problem
class Semigroup s => Semilattice s where
    -- a <> b = b <> a - commutativity
    -- a <> a = a - idempotence

-- | Example

data Container = Container {
    clocation :: String,
    ccontent :: Set String
} deriving Show

-- Can we have a semilattice ContainerK that would tell us about current state of Container while
-- a) container location is changing
-- b) container content is changing

data ContainerK = ContainerK (Maybe LocationK) ContentK deriving Show

instance Semigroup ContainerK where
    (ContainerK l1 c1) <> (ContainerK l2 c2) = ContainerK (l1 <> l2) (c1 <> c2)

data LocationK = LocationK UTCTime String deriving Show

instance Semigroup LocationK where
    l1@(LocationK t1 _) <> l2@(LocationK t2 _) = if t1 > t2 then l1 else l2

data ContentK = ContentK (Set String) deriving Show

instance Semigroup ContentK where
    (ContentK c1) <> (ContentK c2) = ContentK $ c1 <> c2

changeLocation :: UTCTime -> String -> ContainerK
changeLocation t l = ContainerK (Just (LocationK t l)) (ContentK empty)

changeContent :: String -> ContainerK
changeContent s = ContainerK Nothing (ContentK $ singleton s)

someTime :: String -> UTCTime
someTime = parseTimeOrError False defaultTimeLocale "%s"

getContainer :: ContainerK -> Maybe Container
getContainer (ContainerK ml (ContentK c)) = Container <$> ((\(LocationK _ l) -> l) <$> ml) <*> pure c

test :: Maybe Container
test = getContainer $ changeLocation (someTime "10") "2" <> changeContent "a" <> changeLocation (someTime "5") "1" <> changeContent "b"


