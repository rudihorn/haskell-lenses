{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables, TypeApplications,
             AllowAmbiguousTypes, KindSignatures, DataKinds, TypeOperators,
             TypeInType, GADTs, UndecidableInstances, ConstraintKinds #-}

module Lens.Put.Classic where

import Control.DeepSeq
import GHC.TypeLits
import Data.Type.Set (Proxy(..), (:++))
import Data.ByteString.Builder(toLazyByteString)
import Database.PostgreSQL.Simple.FromRow (FromRow(..))

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Common
import Lens.FunDep.Affected (Affected, affected, toDPList, ToDynamic)
import Delta (positive, negative, Delta, delta_union, (#-), (#+))
import Lens.Predicate.Dynamic (DPhrase)
import Lens.Predicate.Hybrid (HPhrase(..))
import FunDep
-- import FunDep (FunDep(..), Left, Right, TopologicalSort)
import Label (IsSubset, AdjustOrder, Subtract)
import Lens (setDebugTime, Droppable, Joinable, Selectable, Lens(..), TableKey, Rt, Fds, Ts)
import Lens.Database.Base (LensDatabase(..), LensQuery, Columns, get, query, query_ex, execute)
import Lens.Database.Query (build_delete, build_delete_all, build_insert, build_update, column_map, query_predicate)
import Lens.Record.Base (Env, InterCols, Project, ProjectEnv, VarsEnv)
import Lens.Record.Sorted (join, merge, revise_fd, project, Revisable, RecordsSet, RecordsDelta)
import Tables (RecoverTables, recover_tables)

import qualified Delta
import qualified Lens.Predicate.Dynamic as DP
import qualified Lens.Predicate.Base as P
import qualified Lens.Record.Base as R
import qualified Lens.Record.Sorted as SR
import qualified Value

put_classic_drop ::
  (RecoverTables (Ts s), R.RecoverEnv (Rt s), LensQuery c,
   Droppable env (key :: [Symbol]) s snew) =>
  c -> (Proxy key) -> (Proxy env) -> (Lens s) -> (Lens snew)
    -> RecordsSet (Rt snew) -> IO (RecordsSet (Rt s))
put_classic_drop c (Proxy :: Proxy key) (Proxy :: Proxy env) (l1 :: Lens s1) _ n =
  do old <- get c l1
     let mprime = join n envRows
     return $ revise_fd @(key --> P.Vars env) mprime old where
  envRows = Set.fromList [P.toRow @env]

put_classic_join ::
  (LensQuery c, Joinable s1 s2 snew joincols) =>
  c -> (Lens s1) -> (Lens s2) -> (Lens snew) -> RecordsSet (Rt snew)
    -> IO (RecordsSet (Rt s1), RecordsSet (Rt s2))
put_classic_join c (l1 :: Lens s1) (l2 :: Lens s2) _ o =
  do m <- get c l1
     n <- get c l2
     let m0 = merge @(TopologicalSort (Fds s1)) m oleft
     let n0 = merge @(TopologicalSort (Fds s2)) n oright
     let l = join m0 n0 `Set.difference` o
     let m' = m0 `Set.difference` (project @(VarsEnv (Rt s1)) l)
     return (m', n0)
     where
  oleft = project @(VarsEnv (Rt s1)) o
  oright = project @(VarsEnv (Rt s2)) o

put_classic_select ::
  (LensQuery c, Selectable p s snew, RecoverTables (Ts s), R.RecoverEnv (Rt s)) =>
  c -> (HPhrase p) -> (Lens s) -> (Lens snew) -> RecordsSet (Rt snew)
    -> IO (RecordsSet (Rt s))
put_classic_select c (HPred p) (l :: Lens s) _ n =
  do m <- get c l
     let unsat = SR.filter (DP.not p) m
     let m0 = merge @(TopologicalSort (Fds s)) unsat n
     return m0

put_classic :: forall c s.
  (RecoverTables (Ts s), R.RecoverEnv (Rt s), LensQuery c, LensDatabase c) =>
  c -> (Lens s) -> RecordsSet (Rt s) -> IO ()
put_classic c (Prim :: Lens s) view =
  do qdelete <- build_delete_all c tbl
     action qdelete
     if Set.null view
       then return ()
       else
         do qinsert <- build_insert c tbl $ Set.toList view
            action qinsert where
  tbl = head $ recover_tables @(Ts s) Proxy
  action = if False then Prelude.print else execute c
put_classic c (Debug l) view =
  do Prelude.print $ show view
     put_classic c l view
put_classic c dl@(DebugTime _ l) view =
  do SR.eval_strict view
     setDebugTime dl
     put_classic c l view
put_classic c l@(Drop key env l1) n =
  do res <- put_classic_drop c key env l1 l n
     put_classic c l1 res
put_classic c l@(Select p l1) n =
  do res <- put_classic_select c p l1 l n
     put_classic c l1 res
put_classic c l@(Join l1 l2) o =
  do (m', n') <- put_classic_join c l1 l2 l o
     put_classic c l1 m'
     put_classic c l2 n'

put_classic_wif :: forall c s.
  (RecoverTables (Ts s), R.RecoverEnv (Rt s), LensQuery c, LensDatabase c) =>
  c -> (Lens s) -> RecordsSet (Rt s) -> IO ()
put_classic_wif c (Prim :: Lens s) view =
  do qdelete <- build_delete_all c tbl
     action qdelete
     if Set.null view
       then return ()
       else
         do qinsert <- build_insert c tbl $ Set.toList view
            action qinsert where
  tbl = head $ recover_tables @(Ts s) Proxy
  action = if True then Prelude.print else execute c
put_classic_wif c (Debug l) view =
  do Prelude.print $ show view
     put_classic c l view
put_classic_wif c dl@(DebugTime _ l) view =
  do let () = Set.toList view `deepseq` ()
     setDebugTime dl
     put_classic c l view
put_classic_wif c l@(Drop key env l1) n =
  do res <- put_classic_drop c key env l1 l n
     put_classic c l1 res
put_classic_wif c l@(Select p l1) n =
  do res <- put_classic_select c p l1 l n
     put_classic c l1 res
put_classic_wif c l@(Join l1 l2) o =
  do (m', n') <- put_classic_join c l1 l2 l o
     put_classic c l2 n'
     put_classic c l1 m'
