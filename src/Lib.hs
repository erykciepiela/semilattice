module Lib where

import Data.Time
import Data.Time.Format
import Data.Set

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


-- | Example

-- Can we have a semilattice Container where
-- a) container location is changing
-- b) container content is changing

data Container = Container {
    containerLocation :: Location,
    containerContent :: Content
} deriving (Show, Eq)

instance Semigroup Container where
    (Container l1 c1) <> (Container l2 c2) = Container (l1 <> l2) (c1 <> c2)

instance Monoid Container where
    mempty = Container mempty mempty 

instance Semilattice Container


data Loc = Loc UTCTime String deriving (Show, Eq)

instance Semigroup Loc where
    l1@(Loc t1 _) <> l2@(Loc t2 _) = if t1 > t2 then l1 else l2


data Location = Location {
    locationLoc :: (Maybe Loc) 
} deriving (Show, Eq)

instance Semigroup Location where
    (Location m1) <> (Location m2) = Location $ m1 <> m2

instance Monoid Location where 
    mempty = Location mempty


data Content = Content {
    contentSet :: Set String
} deriving (Show, Eq)

instance Semigroup Content where
    (Content c1) <> (Content c2) = Content $ c1 <> c2

instance Monoid Content where
    mempty = Content empty


-- events
locationSet :: UTCTime -> String -> Container
locationSet t l = Container (Location (Just (Loc t l))) mempty

contentAdded :: String -> Container
contentAdded s = Container mempty (Content (singleton s))

-- goals
content :: Set String -> Container
content s = Container mempty (Content s)

location :: UTCTime -> String -> Container
location t l = Container (Location (Just (Loc t l))) mempty

--
test :: Bool
test = areAchieved' [content (fromList ["b", "a"]), location (someTime 9) "2"] [locationSet (someTime 10) "2", contentAdded "a", locationSet (someTime 5) "1", contentAdded "b"]

someTime :: Int -> UTCTime
someTime = parseTimeOrError False defaultTimeLocale "%s" . show
    
