{-# LANGUAGE ScopedTypeVariables, GADTs, AllowAmbiguousTypes, TypeApplications,
             ConstraintKinds, PolyKinds, DataKinds, MultiParamTypeClasses,
             KindSignatures #-}

module Lens.Database.Base where

import Data.Text.Lazy.Builder (Builder)
import Data.Type.Set (Proxy(..))
import Database.PostgreSQL.Simple.FromRow (FromRow(..))

import qualified Data.Map.Strict as Map

import Lens (Lens, Ts, Rt)
import Tables (RecoverTables)
import Lens.Record.Base (Env, Row, RecoverEnv)

import qualified Lens.Types as T
import qualified Lens.Predicate.Dynamic as DP

type Tables = [String]
type Columns = Map.Map String ([String], T.Type)
type LensQueryable s = (RecoverTables (Ts s), RecoverEnv (Rt s))

class LensDatabase c where
  escapeId :: c -> String -> IO Builder
  escapeStr :: c -> String -> IO Builder

class LensQuery c where
  query :: forall s rt. (LensQueryable s, rt ~ Rt s, FromRow (Row rt)) =>
    c -> Lens s -> IO [Row rt]
  query_ex :: (FromRow (Row rt), RecoverEnv rt) => Proxy rt -> c -> Tables -> Columns -> DP.Phrase -> IO [Row rt]
  execute :: c -> Builder -> IO ()

query_ex' :: forall c rt. (RecoverEnv rt, LensQuery c, FromRow (Row rt)) =>
  c -> Tables -> Columns -> DP.Phrase -> IO [Row rt]
query_ex' c t cols_map p = query_ex @c @rt Proxy c t cols_map p

type LensGet s c = (LensQueryable s, FromRow (Row (Rt s)), LensQuery c)

get :: forall s c. LensGet s c => c -> Lens s -> IO [Row (Rt s)]
get c l = query c l
