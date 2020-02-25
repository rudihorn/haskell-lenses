{-# LANGUAGE ScopedTypeVariables, GADTs, AllowAmbiguousTypes, TypeApplications,
             ConstraintKinds, PolyKinds, DataKinds, MultiParamTypeClasses,
             KindSignatures #-}

module LensDatabase where

import Data.Text.Lazy.Builder (Builder)
import Data.Type.Set (Proxy(..))
import Database.PostgreSQL.Simple.FromRow

import qualified Data.Map.Strict as Map

import Lens (Lens)
import Tables (RecoverTables)
import RowType (Env, Row, RecoverEnv)

import qualified Types
import qualified DynamicPredicate as DP

type Tables = [String]
type Columns = Map.Map String ([String], Types.Type)
type LensQueryable t r p = (RecoverTables t, RecoverEnv r)

class LensDatabase c where
  escapeId :: c -> String -> IO Builder
  escapeStr :: c -> String -> IO Builder

class LensQuery c where
  query :: forall t rt p fds. (LensQueryable t rt p, FromRow (Row rt)) =>
    c -> Lens t rt p fds -> IO [Row rt]
  query_ex :: (FromRow (Row rt), RecoverEnv rt) => Proxy rt -> c -> Tables -> Columns -> DP.Phrase -> IO [Row rt]

query_ex' :: forall c rt. (RecoverEnv rt, LensQuery c, FromRow (Row rt)) =>
  c -> Tables -> Columns -> DP.Phrase -> IO [Row rt]
query_ex' c t cols_map p = query_ex @c @rt Proxy c t cols_map p
