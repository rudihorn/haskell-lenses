{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications, OverloadedStrings #-}

module Lens.Database.Query where

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

import Control.Monad.State.Lazy
import Data.Type.Set
import Data.Maybe
import Data.Text.Buildable(Buildable)
import Data.Text.Format
import Data.Text.Lazy.Builder

import Common
import Lens (Lens(..), Ts, Rt)
import Lens.FunDep.Affected (ToDynamic, toDPList, toDynamic)
import Lens.Predicate.Hybrid (HPhrase(..))
import Tables (RecoverTables, recover_tables)
import Lens.Record.Base (Row, VarsEnv, RecoverEnv, recover_env)
import Lens.Database.Base (LensQueryable, LensDatabase(..), Columns)
import Lens.Record.Sorted (RecordsSet)
import Lens.Helpers.Format(build_sep_comma, build_sep_space)

import qualified Lens.Types as T
import qualified Lens.Predicate.Base as P
import qualified Lens.Predicate.Dynamic as DP
import qualified Lens.Predicate.Precedence as QP

type ColumnsOpt = Map.Map String (String, String)

class ColumnMap a where
  column_map :: a -> Columns

instance (RecoverTables (Ts s), RecoverEnv (Rt s)) => ColumnMap (Lens s) where
  column_map (Prim) = Map.fromList $ map f env where
    env = recover_env @(Rt s) Proxy
    f (col, typ) = (col, ([table_name], typ))
    table_name = head $ recover_tables @(Ts s) Proxy
  column_map (Debug l) = column_map l
  column_map (Select _ l) = column_map l
  column_map (Drop Proxy Proxy l) = column_map l
  column_map (Join l1 l2) = Map.unionWith f (column_map l1) (column_map l2) where
    f (t1, typ) (t2, _) = (t1 ++ t2, typ)

class QueryPredicate a where
  query_predicate :: a -> DP.Phrase

instance QueryPredicate (Lens s) where
  query_predicate Prim = P.Constant (DP.Bool True)
  query_predicate (Debug l) = query_predicate l
  query_predicate (Drop Proxy Proxy l) = query_predicate l
  query_predicate (Select (HPred pr) l) = DP.simplify $ P.InfixAppl (P.LogicalAnd) pr (query_predicate l)
  query_predicate (Join l1 l2) = DP.simplify $ P.InfixAppl (P.LogicalAnd) (query_predicate l1) (query_predicate l2)

print_op :: P.Operator -> String
print_op P.Plus = "+"
print_op P.LogicalAnd = "AND"
print_op P.LogicalOr = "OR"
print_op P.Equal = "="
print_op P.LessThan = "<"
print_op P.GreaterThan = ">"

print_unary_op :: P.UnaryOperator -> String
print_unary_op P.Negate = "NOT"
print_unary_op P.UnaryMinus = "-"

eq_priority :: QP.Op -> QP.Op -> Builder -> Builder
eq_priority pr npr bld
  | compare npr pr == LT = build "({})" $ Only $ bld
  | otherwise = bld

gr_priority :: QP.Op -> QP.Op -> Builder -> Builder
gr_priority pr npr bld
  | compare npr pr == GT = bld
  | otherwise = build "({})" $ Only $ bld


print_value :: LensDatabase db => db -> DP.Value -> IO Builder
print_value db (DP.Bool False) = return $ build "FALSE" ()
print_value db (DP.Bool True) = return $ build "TRUE" ()
print_value db (DP.Int i) = return $ build "{}" (Only i)
print_value db (DP.String s) = escapeStr db s

print_col :: LensDatabase db => db -> String -> String -> IO Builder
print_col db tbl col =
  do etbl <- escapeId db tbl
     ecol <- escapeId db col
     return $ if tbl == "" then ecol else build "{}.{}" (etbl, ecol)

print_col_t :: LensDatabase db => db -> String -> ([String], T.Type) -> IO Builder
print_col_t db v (table,_) =
  print_col db (head table) v

print_query :: LensDatabase db => db -> ColumnsOpt -> DP.Phrase -> QP.Op -> IO Builder
print_query db _ (P.Constant val) _ = print_value db val
print_query db cols (P.Var v) _ = print_col db tbl col where
  (col, tbl) = fromJust $ Map.lookup v cols
print_query db cols (P.InfixAppl op a b) pr =
  let npr = QP.of_op op in
  do left <- print_query db cols a npr
     right <- print_query db cols b npr
     return $ eq_priority pr npr $ build "{} {} {}" (left, print_op op, right)
print_query db cols (P.UnaryAppl op a) pr =
  let npr = QP.of_unary_op op in
  do arg <- print_query db cols a npr
     return $ gr_priority pr npr $ build "{} {}" (print_unary_op op, arg)
print_query db _ (P.In _ []) _ =
  return $ build "FALSE" ()
print_query db cols (P.In cs vals) pr =
  do vals <- mapM (build_vals) vals
     pcs <- mapM (\v -> print_query db cols (P.Var v) pr) cs
     return $ build "({}) IN ({})" (build_sep_comma pcs, build_sep_comma vals) where
  build_vals vs =
    do vals <- mapM (print_value db) vs
       return $ build "({})" $ Only $ build_sep_comma vals
print_query db cols (P.Case inp cases other) _ =
  do inp <- build_inp inp
     cases <- mapM build_case cases
     other <- print_query db cols other QP.first
     return $ build "CASE {}{} ELSE {} END" (inp, build_sep_space cases, other) where
  build_inp Nothing = return $ build "" ()
  build_inp (Just x) = build "({}) " <$> Only <$> print_query db cols x QP.first
  build_case (key, val) =
     do cond <- print_query db cols key QP.first
        act <- print_query db cols val QP.first
        return $ build "WHEN {} THEN {}" (cond, act)

cols_opt :: Columns -> State (Int,[[String]]) ColumnsOpt
cols_opt cols = do es <- mapM f $ Map.toList cols
                   return (Map.fromList $ concat es) where
  f (k,(tbls,_)) = entries k tbls
  fresh = do (id,cols) <- get
             put (id + 1, cols)
             return $ "__" ++ show id
  add_eqs cs = do (id, cols) <- get
                  put (id, cs : cols)
                  return ()
  fresh_entries col tbl = do id <- fresh
                             return $ entry id col tbl
  entry k col tbl = (k, (col, tbl))
  entries k tbls = do others <- mapM (fresh_entries k) $ tail tbls
                      add_eqs $ k : map fst others
                      return $ entry k k (head tbls) : others

build_query_ex :: forall r db.
  (LensDatabase db) => db -> [String] -> [String] -> Columns -> DP.Phrase -> IO Builder
build_query_ex db tbls cols cols_map p =
    do sel <- cols_bld
       from <- tbls_bld
       wher <- pred_bld
       return $ build "SELECT {} FROM {} WHERE {}" (sel, from, wher) where
  (cols', (_, grps)) = runState (cols_opt cols_map) (1,[])
  build_group (x : y : xs) = P.InfixAppl P.Equal (P.Var x) (P.Var y) : build_group (y : xs)
  build_group _ = []
  build_groups = DP.conjunction $ map DP.conjunction $ map build_group grps
  cols_bld = build_sep_comma <$> (mapM (\k -> print_col_t db k $ fromJust $ Map.lookup k cols_map) $ cols)
  pred_bld = print_query db cols' (DP.conjunction [build_groups, p]) QP.first
  tbls_bld = build_sep_comma <$> (mapM (\x -> build "{}" <$> Only <$> (escapeId db x)) tbls)

build_query :: LensQueryable s =>
  LensDatabase db => db -> Lens s -> IO Builder
build_query db (l :: Lens s) = build_query_ex db tbls cols cols_map p where
  p = query_predicate l
  cols = map fst $ recover_env @(Rt s) Proxy
  cols_map = column_map l
  tbls = recover_tables @(Ts s) Proxy


build_insert_ex :: forall db.
  (LensDatabase db) => db -> String -> [String] -> [[DP.Value]] -> IO Builder
build_insert_ex db tbl cols vals =
  do etbl <- escapeId db tbl
     colstr <- build_sep_comma <$> mapM (escapeId db) cols
     valstr <- build_sep_comma <$> mapM build_record vals
     return $ build "INSERT INTO {} ({}) VALUES {}" (etbl, colstr, valstr) where
  build_record rs = build "({})" <$> Only <$> build_sep_comma <$> mapM (print_value db) rs

build_insert ::
  forall db rt. (ToDynamic rt, Recoverable (VarsEnv rt) [String], LensDatabase db) =>
  db -> String -> [Row rt] -> IO Builder
build_insert db tbl rs = build_insert_ex db tbl cols vals where
  vals = toDPList rs
  cols = recover @(VarsEnv rt) @[String] Proxy

build_delete_ex :: forall db. (LensDatabase db) => db -> String -> [(String, DP.Value)] -> IO Builder
build_delete_ex db tbl match =
  do etbl <- escapeId db tbl
     wher <- print_query db colsOpt pred QP.first
     return $ build "DELETE FROM {} WHERE {}" (etbl, wher) where
  colsOpt = Map.fromList $ map (\(k,_) -> (k,(k,""))) match
  pred = DP.conjunction $ map (\(k,v) -> P.InfixAppl P.Equal (P.Var k) (P.Constant v)) match

build_delete :: forall db rt. (ToDynamic rt, Recoverable (VarsEnv rt) [String], LensDatabase db) =>
  db -> String -> Row rt -> IO Builder
build_delete db tbl match = build_delete_ex db tbl matchex where
  cols = recover @(VarsEnv rt) Proxy
  vals = toDynamic match
  matchex = zip cols vals

build_update_ex :: forall db. LensDatabase db =>
  db -> String -> [(String, DP.Value)] -> [(String, DP.Value)] -> IO Builder
build_update_ex db tbl match update =
  do etbl <- escapeId db tbl
     eset <- build_sep_comma <$> mapM fset update
     ewher <- print_query db colsOpt pred QP.first
     return $ build "UPDATE {} SET {} WHERE {}" (etbl, eset, ewher) where
  colsOpt = Map.fromList $ map (\(k,_) -> (k,(k,""))) match
  pred = DP.conjunction $ map (\(k,v) -> P.InfixAppl P.Equal (P.Var k) (P.Constant v)) match
  fset (k,v) =
    do ek <- print_col db "" k
       ev <- print_value db v
       return $ build "{} = {}" (ek, ev)

build_update :: forall db rtm rtu.
  (Recoverable (VarsEnv rtm) [String], ToDynamic rtm,
   Recoverable (VarsEnv rtu) [String], ToDynamic rtu,
   LensDatabase db) =>
  db -> String -> Row rtm -> Row rtu -> IO Builder
build_update db tbl match update =
    build_update_ex db tbl matchex updex where
  colsm = recover @(VarsEnv rtm) Proxy
  colsu = recover @(VarsEnv rtu) Proxy
  dmatch = toDynamic match
  dupd = toDynamic update
  matchex = zip colsm dmatch
  updex = zip colsu dupd
