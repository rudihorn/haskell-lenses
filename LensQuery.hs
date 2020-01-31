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

print_query_eq :: DbHelper -> ColumnsOpt -> DP.Phrase -> QP.Op -> QP.Op -> IO Builder
print_query_eq db col p pr npr | compare npr pr == LT = build "({})" <$> Only <$> print_query db col p npr
                             | otherwise = print_query db col p npr

print_query_gr :: DbHelper -> ColumnsOpt -> DP.Phrase -> QP.Op -> QP.Op -> IO Builder
print_query_gr db col p pr npr
    | compare npr pr == GT = print_query db col p npr
    | otherwise = build "({})" <$> Only <$> print_query db col p npr

build_sep :: (Buildable sep, Buildable a) => sep -> [a] -> Builder
build_sep _ [] = build "" ()
build_sep _ [x] = build "{}" (Only x)
build_sep sep (x : xs) = build "{}{}{}" (x, sep, build_sep sep xs)

build_sep_str :: Buildable a => String -> [a] -> Builder
build_sep_str sep xs = build_sep sep xs

type DbHelper = (String -> IO Builder, String -> IO Builder)

escId (f,_) = f
escStr (_,g) = g

print_value :: DbHelper -> DP.Value -> IO Builder
print_value db (DP.Bool False) = return $ build "FALSE" ()
print_value db (DP.Bool True) = return $ build "TRUE" ()
print_value db (DP.Int i) = return $ build "{}" (Only i)
print_value db (DP.String s) = build "{}" <$> Only <$> escStr db s

print_col :: DbHelper -> String -> ([String], Types.Type) -> IO Builder
print_col db v (table,_) =
  do tbl <- escId db $ head table
     col <- escId db v
     return $ build "{}.{}" (tbl, col)

print_query :: DbHelper -> ColumnsOpt -> DP.Phrase -> QP.Op -> IO Builder
print_query db _ (P.Constant val) _ = print_value db val
print_query db cols (P.Var v) _ = build "{}.{}" <$> (escIds $ fromJust $ Map.lookup v cols) where
  escIds (x,y) = (,) <$> escId db y <*> escId db x
print_query db cols (P.InfixAppl op a b) pr =
  let npr = QP.of_op op in
  do left <- print_query_eq db cols a pr npr
     right <- print_query_eq db cols b pr npr
     return $ build "{} {} {}" (left, print_op op, right)
print_query db cols (P.UnaryAppl op a) pr =
  let npr = QP.of_unary_op op in
  do arg <- print_query_gr db cols a pr npr
     return $ build "{} {}" (print_unary_op op, arg)
print_query db _ (P.In _ []) _ =
  return $ build "FALSE" ()
print_query db _ (P.In cs vals) _ =
  do vals <- mapM (build_vals) vals
     return $ build "({}) IN ({})" (build_sep_str ", " cs, build_sep_str ", " $ vals) where
  build_vals vs =
    do vals <- mapM (print_value db) vs
       return $ build "({})" $ Only $ build_sep_str ", " $ vals
print_query db cols (P.Case inp cases other) _ =
  do inp <- build_inp inp
     cases <- mapM build_case cases
     other <- print_query db cols other QP.first
     return $ build "CASE {}{} ELSE {} END" (inp, build_sep_str " " $ cases, other) where
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

type LensQueryable t r p = (RecoverTables t, RecoverEnv r, Recoverable p DP.Phrase)

build_query :: LensQueryable t r p =>
  DbHelper -> Lens t r p fds -> IO Builder
build_query db (l :: Lens t r p fds) =
    do sel <- cols_bld
       from <- tbls_bld
       wher <- pred_bld
       return $ build "SELECT {} FROM {} WHERE {}" (sel, from, wher) where
  cols = column_map l
  (cols', (_, grps)) = runState (cols_opt cols) (1,[])
  build_group (x : y : xs) = P.InfixAppl P.Equal (P.Var x) (P.Var y) : build_group (y : xs)
  build_group _ = []
  build_groups = DP.conjunction $ map DP.conjunction $ map build_group grps
  cols_bld = build_sep_str ", " <$> (mapM (\k -> print_col db k $ fromJust $ Map.lookup k cols) $ map fst $ recover_env (Proxy :: Proxy r))
  pred_bld = print_query db cols' (DP.conjunction [build_groups, query_predicate l]) QP.first
  tbls_bld = build_sep_str ", " <$> (mapM (\x -> build "{}" <$> Only <$> (escId db x)) tbls)
  tbls = recover_tables (Proxy :: Proxy t)


