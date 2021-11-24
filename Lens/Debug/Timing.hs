{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeApplications, DataKinds,
             AllowAmbiguousTypes, OverloadedLabels #-}

module Lens.Debug.Timing where

import Control.DeepSeq
import Data.Maybe (fromJust)
import Data.IORef (newIORef, readIORef, writeIORef, modifyIORef, IORef)
import Data.Time.Clock (getCurrentTime, nominalDiffTimeToSeconds, diffUTCTime, UTCTime)
import Lens
import Lens.Database.Base (LensDatabase(..), LensQuery(..))
import Lens.Predicate.Base

data Timing where
  Empty :: Timing
  Time :: UTCTime -> Timing -> Timing
  Split :: Timing -> Timing -> Timing

instance Show Timing where
  show Empty = "*"
  show (Time t tm) = show tm ++ " -> " ++ show t
  show (Split t1 t2) = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"

timed m =
  do t1 <- getCurrentTime
     a <- m
     t2 <- getCurrentTime
     let df = nominalDiffTimeToSeconds $ diffUTCTime t2 t1
     let t = round $ toRational df * 1e3
     return (t,a)

timing :: Lens s -> IO Timing
timing Prim = return Empty
timing (Debug l) = timing l
timing (DebugTime r l) =
  do t <- readIORef r
     tm <- timing l
     return $ Time t tm
timing (Join _ l1 l2) =
  do t1 <- timing l1
     t2 <- timing l2
     return $ Split t1 t2
timing (Select _ l) = timing l
timing (Drop _ _ l) = timing l

firstAndLast :: Timing -> Maybe (UTCTime, UTCTime)
firstAndLast Empty = Nothing
firstAndLast (Time t tm) = Just $ upd $ firstAndLast tm where
  upd Nothing = (t, t)
  upd (Just (_, t1)) = (t, t1)
firstAndLast (Split tm1 tm2) = pick (firstAndLast tm1) (firstAndLast tm2) where
  pick Nothing t = t
  pick t Nothing = t
  pick (Just (tmin1, tmax1)) (Just (tmin2, tmax2)) =
    Just (min tmin1 tmin2, max tmax1 tmax2)

firstAndLastUnpack :: Timing -> (UTCTime, UTCTime)
firstAndLastUnpack tm = fromJust $ firstAndLast tm

diffToMs :: Integral a => (UTCTime, UTCTime) -> a
diffToMs (t1, t2) = round $ toRational df * 1e3 where
  df = nominalDiffTimeToSeconds $ diffUTCTime t2 t1

timingToMs :: Integral a => Timing -> a
timingToMs tm = diffToMs $ firstAndLastUnpack tm

data TimedDatabase where
  Timed :: (LensDatabase db, LensQuery db, Integral i) => db -> IORef [i] -> Bool -> TimedDatabase

instance LensDatabase TimedDatabase where
  escapeId (Timed db _ _) str = escapeId db str
  escapeStr (Timed db _ _) str = escapeStr db str

instance LensQuery TimedDatabase where
  query (Timed db tm _) l =
    do (t,a) <- timed $ query db l
       modifyIORef tm (\l -> t : l)
       return a
  query_ex pr (Timed db tm _) tables cols_map p =
    do () <- p `deepseq` return ()
       (t, a) <- timed $ query_ex pr db tables cols_map p
       modifyIORef tm (\l -> t : l)
       return a
  execute (Timed db tm True) q =
    do (t, a) <- timed $ execute db q
       modifyIORef tm (\l -> t : l)
       return a
  execute (Timed db tm False) q = execute db q


make_timed_conn :: (LensDatabase db, LensQuery db, Integral i) => db -> IO (IORef [i], TimedDatabase)
make_timed_conn c =
  do io <- newIORef []
     return (io, Timed c io False)
