{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeApplications, DataKinds,
             AllowAmbiguousTypes #-}

module Scratch where

import Affected (affected)
import Database.PostgreSQL.Simple(query_, connect, defaultConnectInfo, connectDatabase, connectUser, connectPassword)
import Database.PostgreSQL.Simple.Types(Query(..), fromQuery)
import Database.PostgreSQL.Simple.Internal(escapeIdentifier, escapeStringConn)
import Database.PostgreSQL.Simple.FromRow
-- import Database.PostgreSQL.Simple.Types
import qualified Types as T
import RowType
import Lens
import LensQuery
import qualified Predicate as P
import qualified DynamicPredicate as DP
import HybridPredicate
import Data.Text.Format
import LensDatabase (LensQueryable)
import LensQueryPostgres (query)
import LensPut
import FunDep
import SortedRecords (RecordsSet, rows)
import Delta (fromSet)
import Data.Set (fromList)
import Tables (RecoverTables)

data Test = Test { name :: String, fileQuota :: Int }

instance FromRow Test where
  fromRow = Test <$> field <*> field

testdb :: (FromRow (Row r), Fields r, LensQueryable t r p) => Lens t r p fds -> IO [Row r]
testdb (l :: Lens t r p fds) = do
  conn <- connect defaultConnectInfo {
    connectDatabase = "links",
    connectUser = "links",
    connectPassword = "links"
  }
  res <- query conn l
  -- mapM_ Prelude.print res
  return res

testput :: (RecoverTables ts, RecoverEnv rt) =>
  Lens ts rt p fds -> RecordsSet rt -> IO ()
testput l delta =
  do conn <- connect defaultConnectInfo {
         connectDatabase = "links",
         connectUser = "links",
         connectPassword = "links"
       }
     put conn l (Delta.fromSet delta)

-- Bohanonn et al. PODS 2016 examples
albums = prim @"albums" @'[ '("album", 'T.String), '("quantity", 'T.Int)]
  @'[ '["album"] --> '["quantity"]]

tracks = prim @"tracks" @'[ '("track", 'T.String), '("date", 'T.Int), '("rating", 'T.Int), '("album", 'T.String)]
  @'[ '["track"] --> '["date", "rating"]]

tracks1 = join albums tracks

tracks2 = dropl @'[ '("date", 'P.Int 2020)] @'["track"] tracks1

tracks3 = select (var @"quantity" !> di 2) tracks2

type Output = '[ '("quantity", 'T.Int), '("date", 'T.Int), '("rating", 'T.Int), '("album", 'T.String)]
type Tracks3 = '[ '("quantity", 'T.Int), '("track", 'T.String), '("rating", 'T.Int), '("album", 'T.String)]

type PredRow = '[ '("quantity", 'T.Int), '("album", 'T.String)]

exampleUnchanged = lrows tracks3
  [ (4, "Lovesong", 5, "Paris"),
    (3, "Lullaby", 3, "Show"),
    (5, "Trust", 4, "Wish")]

examplePut = rows @Tracks3
    [ (3, "Lullaby", 4, "Show"),
      (7, "Lovesong", 5, "Disintegration")]

-- my_hybrid_lenses :: Bool -> Int -> String -> IO [Row Output]
my_hybrid_lenses b i s = do
    testdb tracks3 where
  pred = if b
         then (dynamic @PredRow @'T.Bool (var @"quantity" !> di i))
         else (dynamic @PredRow @'T.Bool (var @"album" != ds s))
  tracks1 = Lens.join albums tracks
  tracks2 = select pred tracks1
  tracks3 = dropl @'[ '("date", 'P.Int 2020)] @'["track"] tracks2

type Fds = '[ '["album"] --> '["quantity"],
              '["quantity"] --> '["date", "rating"]]

affect = do
  res <- testdb tracks3
  q <- DP.print $ affected @Fds $ fromList res
  return q
