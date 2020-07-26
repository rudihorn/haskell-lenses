{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeApplications, DataKinds,
             AllowAmbiguousTypes, OverloadedLabels #-}

module Scratch where

import Data.Set (fromList)
import Database.PostgreSQL.Simple(query_, connect, defaultConnectInfo, connectDatabase, connectUser, connectPassword, Connection)
import Database.PostgreSQL.Simple.Types(Query(..), fromQuery)
import Database.PostgreSQL.Simple.Internal(escapeIdentifier, escapeStringConn)
import Database.PostgreSQL.Simple.FromRow

import Lens.FunDep.Affected (affected)
import Lens.Record.Base (RecoverEnv(..), Row, Fields)
import Lens
import LensQuery
import Lens.Predicate.Hybrid
import Data.Text.Format
import LensDatabase (LensGet, get)
import LensQueryPostgres (PostgresDatabase)
import LensPut
import FunDep
import Lens.Record.Sorted (RecordsSet, rows)
import Delta (fromSet)
import Tables (RecoverTables)

import qualified Lens.Types as T
import qualified Lens.Predicate.Base as P
import qualified Lens.Predicate.Dynamic as DP

db_connect = connect defaultConnectInfo {
    connectDatabase = "links",
    connectUser = "links",
    connectPassword = "links"
  }

test_get :: (Fields r, LensGet t r p fds PostgresDatabase) => Lens t r p fds -> IO [Row r]
test_get (l :: Lens t r p fds) = do
  conn <- db_connect
  res <- get conn l
  -- mapM_ Prelude.print res
  return res

test_put_debug :: (RecoverTables ts, RecoverEnv rt, FromRow (Row rt)) =>
  Lens ts rt p fds -> RecordsSet rt -> IO ()
test_put_debug l rs =
  do conn <- db_connect
     put_wif conn l rs

test_put :: (RecoverTables ts, RecoverEnv rt, FromRow (Row rt)) =>
  Lens ts rt p fds -> RecordsSet rt -> IO ()
test_put l rs =
  do conn <- db_connect
     put conn l rs

-- Bohanonn et al. PODS 2016 examples

type Albums = '[ '("album", String), '("quantity", Int)]

albums = prim @"albums" @Albums
  @'[ '["album"] --> '["quantity"]]

type Tracks = '[
  '("track", String),
  '("date", Int),
  '("rating", Int),
  '("album", String)]

tracks = prim @"tracks" @Tracks
  @'[ '["track"] --> '["date", "rating"]]

tracks1 = join tracks albums

tracks2 = dropl @'[ '("date", 'P.Int 2020)] @'["track"] tracks1

tracks3 = select (#quantity !> di 2) tracks2

type Output = '[ '("quantity", Int), '("date", Int), '("rating", Int), '("album", String)]
type Tracks3 = '[ '("track", String), '("rating", Int), '("album", String), '("quantity", Int)]

type PredRow = '[ '("quantity", Int), '("album", String)]

-- exampleUnchanged = lrows tracks3
--   [ (4, "Lovesong", 5, "Paris"),
--     (3, "Lullaby", 3, "Show"),
--     (5, "Trust", 4, "Wish")]

unchangedAlbums = rows @Albums
  [ ("Show", 3),
    ("Galore", 1),
    ("Paris", 4),
    ("Wish", 5),
    ("Eponymous", 42),
    ("Disintegration", 6)]

unchangedTracks = rows @Tracks
  [ ("Lovesong", 1989, 5, "Galore"),
    ("Lovesong", 1989, 5, "Paris"),
    ("Lullaby", 1989, 3, "Galore"),
    ("Lullaby", 1989, 3, "Show"),
    ("Trust", 1992, 4, "Wish") ]

examplePut = rows @Tracks3
  [ ("Lullaby", 4, "Show", 3),
    ("Lovesong", 5, "Disintegration", 7)]

-- my_hybrid_lenses :: Bool -> Int -> String -> IO [Row Output]
my_hybrid_lenses b i s = do
    test_get tracks3 where
  pred = if b
         then (dynamic @PredRow @Bool (var @"quantity" !> di i))
         else (dynamic @PredRow @Bool (var @"album" != ds s))
  tracks1 = Lens.join tracks albums
  tracks2 = select pred tracks1
  tracks3 = dropl @'[ '("date", 'P.Int 2020)] @'["track"] tracks2

type Fds = '[ '["album"] --> '["quantity"],
              '["quantity"] --> '["date", "rating"]]

affect = do
  res <- test_get tracks3
  q <- DP.print $ affected @Fds $ fromList res
  return q
