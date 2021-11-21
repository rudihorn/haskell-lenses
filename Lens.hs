{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications, QuantifiedConstraints, RankNTypes #-}

module Lens where

import GHC.TypeLits
import Data.Type.Set ((:++), Proxy(..))
import Database.PostgreSQL.Simple.FromRow

import Common
import Data.Time.Clock (getCurrentTime, UTCTime)
import Data.IORef (newIORef, readIORef, writeIORef, IORef)
import Lens.FunDep.Affected (Affected, ToDynamic)
import Lens.Predicate.Compile (LookupMap)
import FunDep
import Lens.Predicate.Hybrid -- (HPhrase)
import Label (NoDuplicates, IsDisjoint, Subset, Subtract, SymAsSet)
import Lens.Predicate.Base ((:&), DefVI, EvalEnvRow, EvalRowType, FTV,
                            HasCols, LJDI, ReplacePredicate, Simplify,
                            SPhrase, TypesBool, Vars)
import Lens.Record.Base (Env, EnvSubset, Project, ProjectEnv, JoinEnv, RecoverEnv,
                         RemoveEnv, OverlappingJoin, VarsEnv, Row)
import Lens.Record.Sorted (Revisable, RevisableFd, RecordsSet, rows)
import Tables (DisjointTables, RecoverTables, Tables)

import qualified Lens.Predicate.Dynamic as DP
import qualified Lens.Types as T
import qualified Lens.Predicate.Base as P
import qualified Lens.Record.Base as R
import qualified Lens.Record.Sorted as RT


type family IsIgnoresOutputs (phrase :: SPhrase) (fds :: [FunDep]) :: Bool where
  IsIgnoresOutputs p fds = IsDisjoint (FTV p) (Outputs fds)

type IgnoresOutputs p fds = IsIgnoresOutputs p fds ~ 'True

type DefaultPredicate = P.B 'True

-- currently only works on tree form fundeps
type family TableKey (rt :: Env) (fds :: [FunDep]) :: [Symbol] where
  TableKey rt fds =
    Roots fds :++
    Subtract (VarsEnv rt) (TransClosure (Roots fds) fds)

type family UpdateColumns (rt :: Env) (fds :: [FunDep]) :: [Symbol] where
  UpdateColumns rt fds = Subtract (VarsEnv rt) (TableKey rt fds)

data Sort where
  Sort :: Tables -> Env -> SPhrase -> [FunDep] -> Sort

-- get tables
type family Ts (s :: Sort) :: Tables where
  Ts ('Sort ts _ _ _) = ts

-- get row type
type family Rt (s :: Sort) :: Env where
  Rt ('Sort _ rt _ _) = rt

-- get predicate
type family P (s :: Sort) :: SPhrase where
  P ('Sort _ _ p _) = p

-- get fun deps
type family Fds (s :: Sort) :: [FunDep] where
  Fds ('Sort _ _ _ fds) = fds

type QueryRow s = Row (Rt s)

type LensCommonExp ts rt p fds =
  (Affected fds rt,
   Revisable (TopologicalSort fds) rt rt,
   RecoverTables ts,
   RecoverEnv rt,
   Recoverable (VarsEnv rt) [String],
   Recoverable fds [([String], [String])],
   R.Fields rt,
   LookupMap rt,
   FromRow (R.Row rt),
   ToDynamic rt,
   NoDuplicates rt)

type LensCommon s =
  (LensCommonExp (Ts s) (Rt s) (P s) (Fds s))

type LensableExp ts rt p fdsnew =
  (Project (TableKey rt fdsnew) rt,
   ToDynamic (ProjectEnv (TableKey rt fdsnew) rt),
   Recoverable (VarsEnv (ProjectEnv (TableKey rt fdsnew) rt)) [String],
   Project (UpdateColumns rt fdsnew) rt,
   ToDynamic (ProjectEnv (UpdateColumns rt fdsnew) rt),
   Recoverable (VarsEnv (ProjectEnv (UpdateColumns rt fdsnew) rt)) [String])

type LensableImplConstraints s =
  (LensableExp (Ts s) (Rt s) (P s) (Fds s),
   LensCommon s)

type Lensable s snew =
  (snew ~ 'Sort (Ts s) (Rt s) (P s) (SplitFDs (Fds s)),
   P.Typ (Rt snew) (P snew) ~ 'Just Bool,
   Subset (Cols (Fds snew)) (VarsEnv (Rt snew)),
   LensableImplConstraints snew)

type JoinImplConstraints ts1 rt1 p1 fds1 ts2 rt2 p2 fds2 rtnew joincols =
  (LensCommon ('Sort ts1 rt1 p1 fds1),
   LensCommon ('Sort ts2 rt2 p2 fds2),
   R.Fields rtnew,
   FromRow (R.Row rtnew),
   ProjectEnv (VarsEnv rt1) rtnew ~ rt1,
   ProjectEnv (VarsEnv rt2) rtnew ~ rt2,
   Project (VarsEnv rt1) rtnew,
   Project (VarsEnv rt2) rtnew,
   Recoverable joincols [String],
   Project joincols rt1,
   Project joincols rt2,
   ToDynamic (ProjectEnv joincols rt1),
   ToDynamic (ProjectEnv joincols rt2),
   RT.Joinable rt1 rt2 rtnew)

type JoinableExp ts1 rt1 p1 fds1 ts2 rt2 p2 fds2 rtnew joincols =
  (rtnew ~ JoinEnv rt1 rt2,
   joincols ~ R.InterCols rt1 rt2,
   DisjointTables ts1 ts2,
   OverlappingJoin rt1 rt2,
   IgnoresOutputs p1 fds1, IgnoresOutputs p2 fds2,
   Subset (VarsEnv rt2) (TransClosure joincols fds2),
   InTreeForm fds1, InTreeForm fds2,
   JoinImplConstraints ts1 rt1 p1 fds1 ts2 rt2 p2 fds2 rtnew joincols)

type Joinable s1 s2 snew joincols =
  (JoinableExp (Ts s1) (Rt s1) (P s1) (Fds s1) (Ts s2) (Rt s2) (P s2) (Fds s2) (Rt snew) joincols,
   snew ~ 'Sort (Ts s1 :++ Ts s2) (JoinEnv (Rt s1) (Rt s2))
                (Simplify (P s1 :& P s2)) (SplitFDs (Fds s1 :++ Fds s2)))

type SelectImplConstraints rt p pred fds =
  (Affected fds rt, LookupMap rt, Revisable (TopologicalSort fds) rt rt,
   FromRow (R.Row rt),
   R.Fields rt)

type SelectableExp p rt pred fds =
  (TypesBool rt p,
   IgnoresOutputs pred fds,
   InTreeForm fds,
   SelectImplConstraints rt p pred fds)

type Selectable p s snew =
  (snew ~ 'Sort (Ts s) (Rt s) (Simplify (p :& (P s))) (Fds s),
   SelectableExp p (Rt s) (P s) (Fds s))

type DropImplConstraints env key rt pred fds rtnew =
  (RT.Joinable rtnew (EvalRowType env) rt, R.Fields rt, R.Fields rtnew,
   RecoverEnv rt,
   EvalEnvRow env, FromRow (R.Row rtnew),
   RevisableFd (key --> Vars env) rt rt,
   RevisableFd (key --> Vars env) rt (R.ProjectEnv (key :++ P.Vars env) rt),
   Recoverable (SymAsSet key) [String],
   Project (SymAsSet key) rtnew,
   Affected '[key --> Vars env] rtnew,
   FromRow (R.Row rt),
   FromRow (R.Row (ProjectEnv (key :++ P.Vars env) rt)),
   RecoverEnv (ProjectEnv (key :++ P.Vars env) rt))

type DroppableExp env key rt pred fds rtnew =
  (EnvSubset (EvalRowType env) rt,
   LJDI (Vars env) pred,
   DefVI env pred,
   Subset (Vars env) (TransClosure key fds),
   DropImplConstraints env key rt pred fds rtnew)

type Droppable env key s snew =
  (snew ~ 'Sort (Ts s) (RemoveEnv (Vars env) (Rt s))
                (Simplify (ReplacePredicate env (P s)))
                (DropColumn (Vars env) (Fds s)),
   DroppableExp env key (Rt s) (P s) (Fds s) (Rt snew))

type Debuggable rt =
  (R.Fields rt)

data Lens (s :: Sort) where
  Prim :: Lensable ('Sort '[table] rt p fds) snew => Lens snew
  Debug :: Debuggable (Rt s) => Lens s -> Lens s
  DebugTime :: IORef UTCTime -> Lens s -> Lens s
  Join :: Joinable s1 s2 snew joincols =>
    Lens s1 ->
    Lens s2 ->
    Lens snew
  Select :: (Selectable p s snew) =>
    HPhrase p ->
    Lens s ->
    Lens snew
  Drop :: Droppable env (key :: [Symbol]) s snew =>
    Proxy key ->
    Proxy env ->
    Lens s ->
    Lens snew

type family RowType l :: Env where
  RowType (Lens s) = Rt s

data FromRowHack (rt :: Env) where
  Hack :: FromRow (R.Row rt) => FromRowHack rt

lrows :: (vars ~ R.TupleType (Rt s), R.ToRow (Rt s) vars) =>
  Lens s -> [vars] -> RecordsSet (Rt s)
lrows (l :: Lens s) vars = rows @(Rt s) vars

lensToFromRowHack :: Lens s -> FromRowHack (Rt s)
lensToFromRowHack Prim = Hack
lensToFromRowHack (Debug l) = lensToFromRowHack l
lensToFromRowHack (DebugTime _ l) = lensToFromRowHack l
lensToFromRowHack (Select _ _) = Hack
lensToFromRowHack (Drop _ _ _) = Hack
lensToFromRowHack (Join _ _) = Hack

prim_pred :: forall table rt fds p fdsnew s snew.
  (s ~ 'Sort '[table] rt p fds,
  Lensable s snew)
  => Lens snew
prim_pred = Prim @table @rt @p @fds

prim :: forall table rt fds fdsnew s snew.
  (s ~ 'Sort '[table] rt DefaultPredicate fds,
  Lensable s snew)
  => Lens snew
prim = Prim @table @rt @DefaultPredicate @fds


select :: forall p s snew.
  (Selectable p s snew) => HPhrase p -> Lens s -> Lens snew
select pred l = Select pred l

debug :: forall s. (R.Fields (Rt s)) => Lens s -> Lens s
debug l = Debug l

debugTime :: forall s. Lens s -> IO (Lens s)
debugTime l =
  do t <- getCurrentTime
     r <- newIORef t
     return $ DebugTime r l

setDebugTime :: Lens s -> IO ()
setDebugTime (DebugTime r _) =
  do t <- getCurrentTime
     writeIORef r t

getDebugTime :: Lens s -> IO UTCTime
getDebugTime (DebugTime r _) = readIORef r

dropl :: forall env (key :: [Symbol]) s snew.
  (Droppable env key s snew) =>
  Lens s -> Lens snew
dropl l = Drop @env @key @s @snew Proxy Proxy l

-- RecoverEnv (Rt s)

join :: Joinable s1 s2 snew joincols =>
    Lens s1 ->
    Lens s2 ->
    Lens snew
join l1 l2 = Join l1 l2

lens1 = prim @"test1" @'[ '("A", Int), '("B", String)] @'[ '["A"] --> '["B"]]
lens2 = select (var @"A" #> i @30) lens1
lens3 = dropl @'[ '("B", 'P.String "test")] @'["A"] lens2
