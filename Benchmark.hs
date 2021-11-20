{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeApplications, DataKinds,
             AllowAmbiguousTypes, OverloadedLabels #-}

module Benchmark where

import Control.Exception (assert)
import GHC.Types (Nat)
import Data.Set as Set
import Data.Set (fromList)
import Data.Text.Format
import Data.Type.Set (Proxy(..))
import Database.PostgreSQL.Simple(query_, connect, defaultConnectInfo, connectDatabase, connectUser, connectPassword, Connection)
import Database.PostgreSQL.Simple.Types(Query(..), fromQuery)
import Database.PostgreSQL.Simple.Internal(escapeIdentifier, escapeStringConn)
import Database.PostgreSQL.Simple.FromRow
import System.Random
import System.CPUTime

import Lens
import Lens.FunDep.Affected (affected)
import Lens.Record.Base (RecoverEnv(..), Row, Fields, fetch, update)
import Lens.Database.Query
import Lens.Predicate.Hybrid
import Lens.Predicate.Base ((:=),Phrase(..))
import Lens.Database.Base (LensGet, get)
import Lens.Database.Table (create_index, setup)
import Lens.Database.Postgres (PostgresDatabase)
import Lens.Put.Classic (put_classic)
import LensPut
import FunDep
import Lens.Record.Sorted (RecordsSet, recs)
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

type T1 = '[ '("a", Int), '("b", Int), '("c", Int)]

t1 = prim @"t1" @T1 @'[ '["a"] --> '["b", "c"]]

type T2 = '[ '("b", Int), '("d", Int)]

t2 = prim @"t2" @T2 @'[ '["b"] --> '["d"]]

t1t2 = join t1 t2

with_db f =
  do c <- db_connect
     f c

init_db c =
  do setup c t1
     setup c t2
     create_index c "fk_b" "t1" "b"

get_t1 = with_db $ (\c -> get c t1)
get_t2 = with_db $ (\c -> get c t2)

rand_num :: Int -> IO Int
rand_num upper = getStdRandom (randomR (1,upper))

gen_t1 n =
  mapM make_record [1..n] where
  make_record a =
    do b <- rand_num (quot n 10)
       c <- rand_num 100
       return (a,b,c)

gen_t2 n =
  mapM make_record [1..n] where
  make_record b =
    do d <- rand_num n
       return (b,d)

fill_t1 n c =
  do dat <- recs <$> gen_t1 n
     put_classic c t1 dat
     return dat

fill_t2 n c =
  do dat <- recs <$> gen_t2 n
     put_classic c t2 dat
     return dat

fill_db n c =
  -- empty t1 first, so FK isn't violated
  do t1 <- fill_t1 0 c
     t2 <- fill_t2 (quot n 10) c
     t1 <- fill_t1 n c
     return (t1, t2)

type Fds = '[ 'FunDep '["a"] '["b"], 'FunDep '["a"] '["c"],
             'FunDep '["b"] '["d"]]

timed m =
  do t1 <- getCPUTime
     a <- m
     t2 <- getCPUTime
     let t = fromIntegral (t2-t1) * 1e-9
     return (t,a)

benchmark_1_lens = select (#c #= i @3) t1t2

benchmark_1 c =
  do d <- get c l
     let dat = Set.map chrec d
     (t1,()) <- timed $ put c l dat
     dbg1 <- get c l
     put c l d -- revert
     (t2,()) <- timed $ put_classic c l dat
     dbg2 <- get c l
     put c l d -- revert
     return (t1,t2)
     where
  l = benchmark_1_lens
  chrec r = if fetch @"b" r < 100 then update @"d" 5 r else r

bench_avg wm n b c =
  do _ <- mapM (\_ -> b c) [1..wm]
     bms <- mapM (\_ -> b c) [1..n]
     return bms

avg_timings t =
  (t1avg / l, t2avg / l) where
  l = fromIntegral $ length t
  t1avg = fold (\(a,_) b -> a+b) t
  t2avg = fold (\(_,a) b -> a+b) t

