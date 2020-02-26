{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables, TypeApplications,
             AllowAmbiguousTypes, KindSignatures, DataKinds, TypeOperators,
             TypeInType, GADTs, UndecidableInstances, ConstraintKinds #-}

module LensPut where

import Data.Type.Set (Proxy(..), (:++))
import Data.ByteString.Builder(toLazyByteString)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Common
import Affected (Affected, affected, toDPList, ToDynamic)
import Delta (positive, negative, Delta, delta_union, (#-), (#+))
import DynamicPredicate (DPhrase)
import FunDep
-- import FunDep (FunDep(..), Left, Right, TopologicalSort)
import HybridPredicate (HPhrase(..))
import Label (IsSubset, AdjustOrder)
import Lens (Droppable, Lens(..))
import LensDatabase (LensDatabase(..), LensQuery, Columns, query, query_ex)
import LensQuery (build_insert, column_map, query_predicate)
import RowType (Env, JoinColumns, Project, ProjectEnv, VarsEnv)
import SortedRecords (join, merge, revise_fd, project, Revisable, RecordsSet, RecordsDelta)
import Tables (RecoverTables, recover_tables)
import Database.PostgreSQL.Simple.FromRow

import qualified Delta
import qualified DynamicPredicate as DP
import qualified Predicate as P
import qualified RowType as R
import qualified SortedRecords as SR
import qualified Value

-- Conversion from sorted records to dynamic phrase values

--data LensPutable c ts rt p fds where
--  PrimPut :: LensQuery c rt => Lens ts rt p fds -> LensPutable c ts rt p fds
--  DropPut :: (Droppable env key rt1 p1 fds1 rt pred fds, LensQuery c rt) => LensPutable c ts rt1 p1 fds1 -> Lens ts rt p fds -> LensPutable c ts rt p fds
--  SelectPut :: (Selectable rt p LensQuery c rt) => LensPutable c ts1 rt1 p1 fds1 -> Lens ts rt p fds -> LensPutable c ts rt p fds

put_delta :: forall c ts rt p fds.
  (RecoverTables ts, R.RecoverEnv rt, LensQuery c, LensDatabase c) =>
  c -> (Lens ts rt p fds) -> RecordsDelta rt -> IO ()

put_delta c Prim delta_m =
  do qinsert <- build_insert c tbl $ positive delta_m
     Prelude.print qinsert where
  --mkMap set = map (\e -> project @(StartingPoints (Lefts fds) (Rights fds)))$ Set.fromList set
  tbl = head $ recover_tables @ts Proxy

put_delta c (Drop (Proxy :: Proxy key) (Proxy :: Proxy env) (l :: Lens ts1 rt1 p1 fds1)) delta_n =
  do aff <- affectedIO
     let res = (revise_fd @(key --> P.Vars env) (positive delta_m) aff,
                revise_fd @(key --> P.Vars env) (negative delta_m) aff)
     put_delta c l res where
  cols = column_map l
  affectedIO = Set.fromList <$>
       query_ex @c @(ProjectEnv (key :++ P.Vars env) rt1) Proxy c tbls cols pred where
    tbls = recover_tables @ts Proxy
  pred = DP.conjunction [affected @'[key --> P.Vars env] $ delta_union delta_n, query_predicate l]
  envRows = Set.fromList [P.toRow @env]
  delta_m =
    (join (positive delta_n) envRows,
     join (negative delta_n) envRows)

put_delta c (Select (HPred p) l) delta_n =
  do unsat <- Set.fromList <$> query_ex @c @rt Proxy c tbls cols pred
     let delta_m0 =
           (Delta.fromSet $ merge @(TopologicalSort fds) unsat (positive delta_n))
           #- Delta.fromSet unsat
     let delta_nh =
           (SR.filter p $ positive delta_m0, SR.filter p $ negative delta_m0)
           #- delta_n
     put_delta c l (delta_m0 #- delta_nh) where
  pred = DP.conjunction
    [affected @fds $ Delta.positive delta_n,
     query_predicate l,
     DP.not $ p]
  cols = column_map l
  tbls = recover_tables @ts Proxy

put_delta c (Join (l1 :: Lens ts1 rt1 p1 fds1) (l2 :: Lens ts2 rt2 p2 fds2)) delta_o =
  do qd1 <- Set.fromList <$> query_ex @c @rt1 Proxy c ts1 (column_map l1) pred_m
     qd2 <- Set.fromList <$> query_ex @c @rt2 Proxy c ts2 (column_map l2) pred_n
     let delta_m0 = Delta.fromSet (merge @(TopologicalSort fds1) qd1 delta_ol) #- Delta.fromSet qd1
     let delta_n' = Delta.fromSet (merge @(TopologicalSort fds2) qd2 delta_or) #- Delta.fromSet qd2
     qM <- Set.fromList <$> query_ex @c @rt1 Proxy c ts1 (column_map l1) (pjoin l1 delta_m0)
     qN <- Set.fromList <$> query_ex @c @rt2 Proxy c ts2 (column_map l2) (pjoin l2 delta_n')
     let delta_l = (join @rt (positive $ Delta.fromSet qM #+ delta_m0) (positive delta_n') `Set.union`
                    join @rt (positive delta_m0) (positive $ Delta.fromSet qN #+ delta_n'),
                    (join @rt (negative delta_m0) qN) `Set.union` (join @rt qM (negative delta_n')))
     let delta_m' = delta_m0 #- (project @(VarsEnv rt1) $ positive delta_l,
                                 project @(VarsEnv rt1) $ negative delta_l)
     put_delta c l1 delta_m'
     put_delta c l2 delta_n' where
  delta_ol = project @(VarsEnv rt1) $ Delta.positive delta_o
  delta_or = project @(VarsEnv rt2) $ Delta.positive delta_o
  pred_m = DP.conjunction [affected @fds1 delta_ol, query_predicate l1]
  pred_n = DP.conjunction [affected @fds2 delta_or, query_predicate l2]
  ts1 = recover_tables @ts1 Proxy
  ts2 = recover_tables @ts2 Proxy
  pjoin :: (Project (JoinColumns rt1 rt2) rtl, ToDynamic (ProjectEnv (JoinColumns rt1 rt2) rtl)) =>
    Lens tsl rtl pl fdsl -> RecordsDelta rtl -> DPhrase
  pjoin (l :: Lens tsl rtl pl fdsl) delta =
    DP.conjunction
      [P.In (recover @(JoinColumns rt1 rt2) Proxy)
         (toDPList $ project @(JoinColumns rt1 rt2) (delta_union delta)),
       query_predicate l]


put :: forall c ts rt p fds.
  (RecoverTables ts, R.RecoverEnv rt, LensQuery c, LensDatabase c, FromRow (R.Row rt)) =>
  c -> (Lens ts rt p fds) -> RecordsSet rt -> IO ()
put c l rs =
  do unchanged <- query c l
     put_delta c l (Delta.fromSet rs #- Delta.fromList unchanged)
