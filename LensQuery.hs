{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications, OverloadedStrings #-}

module LensQuery where

import Common
import qualified Data.Map.Strict as Map
import Data.Type.Set
import Data.Maybe
import Lens
import Types
import Tables
import RowType
import qualified Predicate as P
import qualified DynamicPredicate as DP
import Data.Text.Format
import Data.Text.Lazy.Builder
import qualified QueryPrecedence as QP
import Data.Text.Buildable(Buildable)
import Data.String
import Control.Monad.State.Lazy

type Columns = Map.Map String ([String], Types.Type)
type ColumnsOpt = Map.Map String (String, String)

class ColumnMap a where
  column_map :: a -> Columns

instance (RecoverTables t, RecoverEnv r) => ColumnMap (Lens t r p fds) where
  column_map (Prim) = Map.fromList $ map f env where
    env = recover_env (Proxy :: Proxy r)
    f (col, typ) = (col, ([table_name], typ))
    table_name = head $ recover_tables (Proxy :: Proxy t)
  column_map (Select Proxy l) = column_map l
  column_map (Drop l) = column_map l
  column_map (Join l1 l2) = Map.unionWith f (column_map l1) (column_map l2) where
    f (t1, typ) (t2, _) = (t1 ++ t2, typ)

class QueryPredicate a where
  query_predicate :: a -> DP.Phrase

instance Recoverable p DP.Phrase => QueryPredicate (Lens t r p fds) where
  query_predicate Prim = recover @p Proxy
  query_predicate (Drop l) = query_predicate l
  query_predicate (Select (Proxy :: Proxy pr) l) = DP.simplify $ P.InfixAppl (P.LogicalAnd) (recover @pr Proxy) (query_predicate l)
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

print_query_eq :: ColumnsOpt -> DP.Phrase -> QP.Op -> QP.Op -> Builder
print_query_eq col p pr npr | compare npr pr == LT = build "({})" (Only $ print_query col p npr)
                             | otherwise = print_query col p npr

print_query_gr :: ColumnsOpt -> DP.Phrase -> QP.Op -> QP.Op -> Builder
print_query_gr col p pr npr
    | compare npr pr == GT = print_query col p npr
    | otherwise = build "({})" (Only $ print_query col p npr)

build_sep :: (Buildable sep, Buildable a) => sep -> [a] -> Builder
build_sep _ [] = build "" ()
build_sep _ [x] = build "{}" (Only x)
build_sep sep (x : xs) = build "{}{}{}" (x, sep, build_sep sep xs)

build_sep_str :: Buildable a => String -> [a] -> Builder
build_sep_str sep xs = build_sep sep xs

print_value :: DP.Value -> Builder
print_value (DP.Bool False) = build "FALSE" ()
print_value (DP.Bool True) = build "TRUE" ()
print_value (DP.Int i) = build "{}" (Only i)
print_value (DP.String s) = build "\"{}\"" (Only s)

print_col :: String -> ([String], Types.Type) -> Builder
print_col v (table,_) = build "`{}`.`{}`" (head table, v)

print_query :: ColumnsOpt -> DP.Phrase -> QP.Op -> Builder
print_query _ (P.Constant val) _ = print_value val
print_query cols (P.Var v) _ = build "`{}`.`{}`"  $ fromJust $ Map.lookup v cols where
print_query cols (P.InfixAppl op a b) pr =
  let npr = QP.of_op op in
  build "{} {} {}" (print_query_eq cols a pr npr, print_op op, print_query_eq cols b pr npr)
print_query cols (P.UnaryAppl op a) pr =
  let npr = QP.of_unary_op op in
  build "{} {}" (print_unary_op op, print_query_gr cols a pr npr)
print_query _ (P.In _ []) _ =
  build "FALSE" ()
print_query _ (P.In cs vals) _ =
  build "({}) IN ({})" (build_sep_str ", " cs, build_sep_str ", " $ map build_vals vals) where
  build_vals vs = build "({})" $ Only $ build_sep_str ", " $ map print_value vs
print_query cols (P.Case inp cases other) _ =
  build "CASE {}{} ELSE {} END" (build_inp inp, build_sep_str " " $ map build_case cases, print_query cols other QP.first) where
  build_inp Nothing = build "" ()
  build_inp (Just x) = build "({}) " (Only $ print_query cols x QP.first)
  build_case (key, val) = build "WHEN {} THEN {}" (print_query cols key QP.first, print_query cols val QP.first)

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

build_query :: (RecoverTables t, RecoverEnv r, Recoverable p DP.Phrase) => Lens t r p fds -> Builder
build_query (l :: Lens t r p fds) = build "SELECT {} FROM {} WHERE {}" (cols_bld, tbls_bld, pred_bld) where
  cols = column_map l
  (cols', (_, grps)) = runState (cols_opt cols) (1,[])
  build_group (x : y : xs) = P.InfixAppl P.Equal (P.Var x) (P.Var y) : build_group (y : xs)
  build_group _ = []
  build_groups = DP.conjunction $ map DP.conjunction $ map build_group grps
  cols_bld = build_sep_str ", " $ map (\(k,v) -> print_col k v) $ Map.toList cols
  pred_bld = print_query cols' (DP.conjunction [build_groups, query_predicate l]) QP.first
  tbls_bld = build_sep_str ", " $ map (build "`{}`" . Only) $ tbls
  tbls = recover_tables (Proxy :: Proxy t)

