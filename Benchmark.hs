{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeApplications, DataKinds,
             AllowAmbiguousTypes, OverloadedLabels #-}

module Benchmark where

import Control.Exception (assert)
import GHC.Types (Nat)
import Data.IORef (readIORef, writeIORef)
import Data.Set as Set
import Data.Set (fromList)
import Data.List (sort)
import Data.Text.Format
import Data.Type.Set (Proxy(..))
import Database.PostgreSQL.Simple(query_, connect, defaultConnectInfo, connectDatabase, connectUser, connectPassword, Connection)
import Database.PostgreSQL.Simple.Types(Query(..), fromQuery)
import Database.PostgreSQL.Simple.Internal(escapeIdentifier, escapeStringConn)
import Database.PostgreSQL.Simple.FromRow
import System.Random
import System.CPUTime
import Data.Time.Clock (getCurrentTime, diffUTCTime, nominalDiffTimeToSeconds)

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
import Lens.Put.Incremental (put, put_wif)
import Lens.Debug.Timing (timed, timing, firstAndLast, timingToMs, make_timed_conn)
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
t1dbg = debugTime t1

type T2 = '[ '("b", Int), '("d", Int)]

t2 = prim @"t2" @T2 @'[ '["b"] --> '["d"]]
t2dbg = debugTime t2

t1t2 = join t1 t2
t1t2dbg =
  do t1d <- t1dbg
     t2d <- t2dbg
     return $ join t1d t2d

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

timed_alt m =
  do t1 <- getCPUTime
     a <- m
     t2 <- getCPUTime
     let t = fromIntegral (t2-t1) * 1e-9
     return (t,a)

benchmark_1_lens = select (#c #= i @3) t1t2

benchmark_1 incremental c =
  do l1 <- t1t2dbg
     l <- debugTime $ select (#c #= i @3) l1
     d <- get c l
     let dat = Set.map chrec d
     (t1,()) <- timed $
       if incremental then put c l dat else put_classic c l dat
     tm <- timing l
     put c l d -- revert
     return $ timingToMs tm
     -- return (t1, t2)
     where
  -- l = benchmark_1_lens
  chrec r = if fetch @"b" r < 100 then update @"d" 5 r else r

benchmark_2 incremental c =
  do l1 <- t1dbg
     l <- debugTime $ dropl @'[ '("c", 'P.Int 0)] @'[ "a"] l1
     (tio, tc) <- make_timed_conn c
     d <- get c l
     let dat = Set.map chrec d
     (t1,()) <- timed $
       if incremental then put tc l dat else put_classic tc l dat
     tm <- timing l
     qt <- readIORef tio
     put c l d -- revert
     return $ (qt !! 1, timingToMs tm)
     where
  -- l = benchmark_1_lens
  a r = fetch @"a" r
  chrec r = if 60 < a r && a r <= 80 then update @"b" 5 r else r

benchmark_3 incremental c =
  do l1 <- t1t2dbg
     l <- debugTime $ l1
     (tio, tc) <- make_timed_conn c
     d <- get c l
     let dat = Set.map chrec d
     writeIORef tio []
     (t1,()) <- timed $
       if incremental then put tc l dat else put_classic tc l dat
     tm <- timing l
     qt <- readIORef tio
     Prelude.print qt
     put c l d -- revert
     return $ timingToMs tm
     where
  -- l = benchmark_1_lens
  b r = fetch @"b" r
  chrec r = if 40 < b r && b r <= 50 then update @"c" 5 r else r

bench_avg wm n b c =
  do _ <- mapM (\_ -> b c) [1..wm]
     bms <- mapM (\_ -> b c) [1..n]
     return bms

mean_timings t =
  (t1avg / l, t2avg / l) where
  l = fromIntegral $ length t
  t1avg = fold (\(a,_) b -> a+b) t
  t2avg = fold (\(_,a) b -> a+b) t

median t =
  if mod l 2 > 0 then (t !! i + t !! (i+1)) / 2 else t !! i where
  sorted = sort t
  l = length t
  i = quot l 2

median_timings t =
  (map_median fst, map_median snd) where
  map_median f = median $ fmap f t
