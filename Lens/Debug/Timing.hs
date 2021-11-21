{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeApplications, DataKinds,
             AllowAmbiguousTypes, OverloadedLabels #-}

module Lens.Debug.Timing where

import Data.Maybe (fromJust)
import Data.IORef (newIORef, readIORef, writeIORef, IORef)
import Data.Time.Clock (getCurrentTime, nominalDiffTimeToSeconds, diffUTCTime, UTCTime)
import Lens

data Timing where
  Empty :: Timing
  Time :: UTCTime -> Timing -> Timing
  Split :: Timing -> Timing -> Timing

instance Show Timing where
  show Empty = "*"
  show (Time t tm) = show tm ++ " -> " ++ show t
  show (Split t1 t2) = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"

timing :: Lens s -> IO Timing
timing Prim = return Empty
timing (Debug l) = timing l
timing (DebugTime r l) =
  do t <- readIORef r
     tm <- timing l
     return $ Time t tm
timing (Join l1 l2) =
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
