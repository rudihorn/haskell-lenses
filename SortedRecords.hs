
module SortedRecords where

import RowType (Row)
import Data.Set (Set)
import qualified Data.Set as Set

type SortedRecords a = (Set (Row a), Set (Row a))
