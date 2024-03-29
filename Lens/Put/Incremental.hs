{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables, TypeApplications,
             AllowAmbiguousTypes, KindSignatures, DataKinds, TypeOperators,
             BangPatterns,
             TypeInType, GADTs, UndecidableInstances, ConstraintKinds #-}

module Lens.Put.Incremental where

import Data.Type.Set (Proxy(..), (:++))
import Data.ByteString.Builder(toLazyByteString)
import Database.PostgreSQL.Simple.FromRow (FromRow(..))

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.MultiSet as MSet

import Common
import Control.DeepSeq
import Lens.FunDep.Affected (Affected, affected, toDPList, ToDynamic)
import Delta (positive, negative, Delta, delta_union, (#-), (#+))
import Lens.Predicate.Dynamic (DPhrase)
import Lens.Predicate.Hybrid (HPhrase(..))
import FunDep
-- import FunDep (FunDep(..), Left, Right, TopologicalSort)
import Label (IsSubset, AdjustOrder, Subtract)
import Lens (setDebugTime, delete_left, delete_right, Droppable, DeleteStrategy, Joinable, Lens(..), TableKey, Rt, Fds, Ts)
import Lens.Database.Base (LensDatabase(..), LensQuery, Columns, query, query_ex, execute)
import Lens.Database.Query (build_delete, build_insert, build_update, column_map, query_predicate, run_multiple)
import Lens.Record.Base (Env, InterCols, InterEnv, Project, ProjectEnv, VarsEnv)
import Lens.Record.Sorted (join, merge, revise_fd, project, Revisable, RecordsSet, RecordsDelta)
import Data.Time.Clock (getCurrentTime)
import Lens.Debug.Timing (timed)
import Tables (RecoverTables, recover_tables)

import qualified Delta
import qualified Lens.Predicate.Dynamic as DP
import qualified Lens.Predicate.Base as P
import qualified Lens.Record.Base as R
import qualified Lens.Record.Sorted as SR
import qualified Value

-- Conversion from sorted records to dynamic phrase values

--data LensPutable c ts rt p fds where
--  PrimPut :: LensQuery c rt => Lens ts rt p fds -> LensPutable c ts rt p fds
--  DropPut :: (Droppable env key rt1 p1 fds1 rt pred fds, LensQuery c rt) => LensPutable c ts rt1 p1 fds1 -> Lens ts rt p fds -> LensPutable c ts rt p fds
--  SelectPut :: (Selectable rt p LensQuery c rt) => LensPutable c ts1 rt1 p1 fds1 -> Lens ts rt p fds -> LensPutable c ts rt p fds

put_delta_join_left :: forall c s1 s2 snew joincols.
  (LensQuery c, Joinable s1 s2 snew joincols) =>
  c -> Lens s1 -> Lens s2 -> Lens snew -> RecordsDelta (Rt snew)
    -> IO (RecordsDelta (Rt s1), RecordsDelta (Rt s2))
put_delta_join_left c (l1 :: Lens s1) (l2 :: Lens s2) (_ :: Lens s) delta_o =
  do qd1 <- Set.fromList <$> query_ex @c @(Rt s1) Proxy c ts1 (column_map l1) pred_m
     qd2 <- Set.fromList <$> query_ex @c @(Rt s2) Proxy c ts2 (column_map l2) pred_n
     let delta_m0 = Delta.fromSet (merge @(TopologicalSort (Fds s1)) qd1 delta_ol) #- Delta.fromSet qd1
     let delta_n' = Delta.fromSet (merge @(TopologicalSort (Fds s2)) qd2 delta_or) #- Delta.fromSet qd2
     qM <- Set.fromList <$> query_ex @c @(Rt s1) Proxy c ts1 (column_map l1) (pjoin l1 delta_m0)
     qN <- Set.fromList <$> query_ex @c @(Rt s2) Proxy c ts2 (column_map l2) (pjoin l2 delta_n')
     let delta_l = (join @(Rt s) (positive $ Delta.fromSet qM #+ delta_m0) (positive delta_n') `Set.union`
                    join @(Rt s)(positive delta_m0) (positive $ Delta.fromSet qN #+ delta_n'),
                    (join @(Rt s) (negative delta_m0) qN) `Set.union` (join @(Rt s) qM (negative delta_n')))
                    #- delta_o
     let delta_m' = delta_m0 #- (project @(VarsEnv (Rt s1)) $ positive delta_l,
                                 project @(VarsEnv (Rt s1)) $ negative delta_l)
     return (delta_m', delta_n') where
  delta_ol = project @(VarsEnv (Rt s1)) $ Delta.positive delta_o
  delta_or = project @(VarsEnv (Rt s2)) $ Delta.positive delta_o
  pred_m = DP.conjunction [or_key $ affected @(Fds s1) delta_ol, query_predicate l1]
  pred_n = DP.conjunction [or_key $ affected @(Fds s2) delta_or, query_predicate l2]
  ts1 = recover_tables @(Ts s1) Proxy
  ts2 = recover_tables @(Ts s2) Proxy
  pjoin :: (Project (InterCols (Rt s1) (Rt s2)) (Rt sl), ToDynamic (ProjectEnv (InterCols (Rt s1) (Rt s2)) (Rt sl))) =>
    Lens sl -> RecordsDelta (Rt sl) -> DPhrase
  pjoin (l :: Lens sl) delta =
    DP.conjunction
      [P.In (recover @(InterCols (Rt s1) (Rt s2)) Proxy)
         (toDPList $ Set.toList $ project @(InterCols (Rt s1) (Rt s2)) (delta_union delta)),
       query_predicate l]
 -- workaround for weird affected behavior. When no FDS are available search for identical rows
 -- this should probably search for all keys as well as functional dependencies
  or_key (P.Constant (DP.Bool False)) = P.In (recover @(VarsEnv (Rt s2)) @[String] Proxy) (toDPList $ Set.toList $ delta_or)
  or_key p = p

put_delta_join_templ :: forall c s1 s2 snew joincols.
  (LensQuery c, Joinable s1 s2 snew joincols, R.RecoverEnv (Rt snew), RecoverTables (Ts snew)) =>
  c -> (R.Row (Rt snew) -> DeleteStrategy) -> Lens s1 -> Lens s2 -> Lens snew -> RecordsDelta (Rt snew)
    -> IO (RecordsDelta (Rt s1), RecordsDelta (Rt s2))
put_delta_join_templ c delfn (l1 :: Lens s1) (l2 :: Lens s2) (l :: Lens s) delta_o =
  do qd1 <- Set.fromList <$> query_ex @c @(Rt s1) Proxy c ts1 (column_map l1) pred_m
     qd2 <- Set.fromList <$> query_ex @c @(Rt s2) Proxy c ts2 (column_map l2) pred_n
     let delta_m0 = Delta.fromSet (merge @(TopologicalSort (Fds s1)) qd1 delta_ol) #- Delta.fromSet qd1
     let delta_n0 = Delta.fromSet (merge @(TopologicalSort (Fds s2)) qd2 delta_or) #- Delta.fromSet qd2
     qM <- Set.fromList <$> query_ex @c @(Rt s1) Proxy c ts1 (column_map l1) (pjoin l1 delta_m0)
     qN <- Set.fromList <$> query_ex @c @(Rt s2) Proxy c ts2 (column_map l2) (pjoin l2 delta_n0)
     let delta_l = (join @(Rt s) (positive $ Delta.fromSet qM #+ delta_m0) (positive delta_n0) `Set.union`
                    join @(Rt s)(positive delta_m0) (positive $ Delta.fromSet qN #+ delta_n0),
                    (join @(Rt s) (negative delta_m0) qN) `Set.union` (join @(Rt s) qM (negative delta_n0)))
                    #- delta_o
     (ll,la) <- sort_deletes delta_o $ positive delta_l
     let delta_m' = delta_m0 #- (project @(VarsEnv (Rt s1)) ll, Set.empty)
     let delta_n' = delta_n0 #- (project @(VarsEnv (Rt s2)) la, Set.empty)
     return (delta_m', delta_n') where
  sort_deletes delta_o delta_l_pl =
    if any (delete_right . delfn) delta_l_pl
    then
      do qO <- MSet.fromList <$>
           query_ex @c @(InterEnv (Rt s1) (Rt s2)) Proxy c ts (column_map l) (
           DP.conjunction [query_predicate l,
             P.In (recover @joincols Proxy) (toDPList $ Set.toList $ project @joincols delta_l_pl)])
         -- use multiset semantics here
         let ll = join @(Rt s) delta_l_pl $
                  MSet.toSet $ (qO `MSet.union` (projMSet $ positive delta_o)) MSet.\\ projMSet (negative delta_o)
         let la = delta_l_pl Set.\\ ll
         return (ll `Set.union` Set.filter (delete_left . delfn) la, Set.filter (delete_right . delfn) la)
    else return (delta_l_pl, Set.empty)
  projMSet set = MSet.map (R.project @joincols @(Rt snew)) $ MSet.fromSet set
  delta_ol = project @(VarsEnv (Rt s1)) $ Delta.positive delta_o
  delta_or = project @(VarsEnv (Rt s2)) $ Delta.positive delta_o
  pred_m = DP.conjunction [or_key $ affected @(Fds s1) delta_ol, query_predicate l1]
  pred_n = DP.conjunction [or_key $ affected @(Fds s2) delta_or, query_predicate l2]
  ts1 = recover_tables @(Ts s1) Proxy
  ts2 = recover_tables @(Ts s2) Proxy
  ts = recover_tables @(Ts snew) Proxy
  pjoin :: (Project (InterCols (Rt s1) (Rt s2)) (Rt sl), ToDynamic (ProjectEnv joincols (Rt sl))) =>
    Lens sl -> RecordsDelta (Rt sl) -> DPhrase
  pjoin (l :: Lens sl) delta =
    DP.conjunction
      [P.In (recover @(InterCols (Rt s1) (Rt s2)) Proxy)
         (toDPList $ Set.toList $ project @(InterCols (Rt s1) (Rt s2)) (delta_union delta)),
       query_predicate l]
 -- workaround for weird affected behavior. When no FDS are available search for identical rows
 -- this should probably search for all keys as well as functional dependencies
  or_key (P.Constant (DP.Bool False)) = P.In (recover @(VarsEnv (Rt s2)) @[String] Proxy) (toDPList $ Set.toList $ delta_or)
  or_key p = p





put_delta :: forall c s.
  (RecoverTables (Ts s), R.RecoverEnv (Rt s), LensQuery c, LensDatabase c) =>
  c -> (Lens s) -> RecordsDelta (Rt s) -> Bool -> IO ()

put_delta c (Prim :: Lens s) delta_m what_if =
  do qdelete <- mapM (build_delete c tbl) $ Map.keys mapDel
     qupdate <- mapM (\(k,e) ->
       build_update c tbl k (R.project @(Subtract (VarsEnv (Rt s)) (TableKey (Rt s) (Fds s))) e))
       $ Map.assocs mapUpd
     v <- run_multiple action qupdate
     v <- run_multiple action qdelete
     if List.null insElems
       then return ()
       else
         do qinsert <- build_insert c tbl $ insElems
            action qinsert where
  insElems = Map.elems mapIns
  mkMap set = Map.fromList $ map (\e -> (R.project @(TableKey (Rt s) (Fds s)) @(Rt s) e, e)) $ Set.toList set
  mapPos = mkMap $ positive delta_m
  mapNeg = mkMap $ negative delta_m
  mapIns = mapPos Map.\\ mapNeg
  mapDel = mapNeg Map.\\ mapPos
  mapUpd = mapPos `Map.intersection` mapNeg
  tbl = head $ recover_tables @(Ts s) Proxy
  action = if what_if then Prelude.print else execute c

put_delta c (Debug l) delta_m wif =
  do Prelude.print $ show delta_m
     put_delta c l delta_m wif

put_delta c dl@(DebugTime _ l) delta_m wif =
  do SR.eval_strict_delta delta_m
     setDebugTime dl
     put_delta c l delta_m wif

put_delta c (Drop (Proxy :: Proxy key) (Proxy :: Proxy env) (l :: Lens s1)) delta_n wif =
  do aff <- affectedIO
     let res = (revise_fd @(key --> P.Vars env) (positive delta_m) aff,
                revise_fd @(key --> P.Vars env) (negative delta_m) aff)
     put_delta c l res wif where
  cols = column_map l
  affectedIO = Set.fromList <$>
       query_ex @c @(ProjectEnv (key :++ P.Vars env) (Rt s1)) Proxy c tbls cols pred where
    tbls = recover_tables @(Ts s) Proxy
  pred = DP.conjunction [affected @'[key --> P.Vars env] $ delta_union delta_n, query_predicate l]
  envRows = Set.fromList [P.toRow @env]
  delta_m =
    (join (positive delta_n) envRows,
     join (negative delta_n) envRows)

put_delta c (Select (HPred p) l) delta_n wif =
  do unsat <- Set.fromList <$> query_ex @c @(Rt s) Proxy c tbls cols pred
     let delta_m0 =
           ((Delta.fromSet $ merge @(TopologicalSort (Fds s)) unsat (positive delta_n))
           #- Delta.fromSet unsat) #- (Delta.fromSet $ negative delta_n)
     let delta_nh =
           (SR.filter p $ positive delta_m0, SR.filter p $ negative delta_m0)
           #- delta_n
     put_delta c l (delta_m0 #- delta_nh) wif where
  pred = DP.conjunction
    [affected @(Fds s) $ Delta.positive delta_n,
     query_predicate l,
     DP.not $ p]
  cols = column_map l
  tbls = recover_tables @(Ts s) Proxy

put_delta c l@(Join delfn (l1 :: Lens s1) (l2 :: Lens s2)) delta_o wif =
  do (delta_m, delta_n) <- put_delta_join_templ c delfn l1 l2 l delta_o
     put_delta c l1 delta_m wif
     put_delta c l2 delta_n wif

type LensPut c s =
  (RecoverTables (Ts s), R.RecoverEnv (Rt s), LensQuery c,
   LensDatabase c, FromRow (R.Row (Rt s)), NFData (R.Row (Rt s)))

put :: forall c s. LensPut c s =>
  c -> Lens s -> RecordsSet (Rt s) -> IO ()
put c l rs =
  do unchanged <- query c l
     let delta = Delta.fromSet rs #- Delta.fromList unchanged
     put_delta c l delta False

put_wif :: forall c s. LensPut c s =>
  c -> Lens s -> RecordsSet (Rt s) -> IO ()
put_wif c l rs =
  do unchanged <- query c l
     let delta = Delta.fromSet rs #- Delta.fromList unchanged
     put_delta c l delta True

