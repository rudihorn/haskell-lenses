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
import Lens.Record.Base (Env, Row, RecoverEnv)

import qualified Lens.Types as T
import qualified Lens.Predicate.Dynamic as DP

type Tables = [String]
type Columns = Map.Map String ([String], T.Type)
type LensQueryable t r p = (RecoverTables t, RecoverEnv r)

class LensDatabase c where
  escapeId :: c -> String -> IO Builder
  escapeStr :: c -> String -> IO Builder

class LensQuery c where
  query :: forall t rt p fds. (LensQueryable t rt p, FromRow (Row rt)) =>
    c -> Lens t rt p fds -> IO [Row rt]
  query_ex :: (FromRow (Row rt), RecoverEnv rt) => Proxy rt -> c -> Tables -> Columns -> DP.Phrase -> IO [Row rt]
  execute :: c -> Builder -> IO ()

query_ex' :: forall c rt. (RecoverEnv rt, LensQuery c, FromRow (Row rt)) =>
  c -> Tables -> Columns -> DP.Phrase -> IO [Row rt]
query_ex' c t cols_map p = query_ex @c @rt Proxy c t cols_map p

type LensGet t rt p fds c = (LensQueryable t rt p, FromRow (Row rt), LensQuery c)

get :: forall t rt p fds c. LensGet t rt p fds c => c -> Lens t rt p fds -> IO [Row rt]
get c l = query c l
