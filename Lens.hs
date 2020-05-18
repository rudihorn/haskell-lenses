{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications #-}

module Lens where

import GHC.TypeLits
import Data.Type.Set ((:++), Proxy(..))
import Database.PostgreSQL.Simple.FromRow

import Common
import Affected (Affected, ToDynamic)
import CompilePredicate (LookupMap)
--import FunDep (DropColumn, FunDep, InTreeForm, SplitFDs, Outputs)
import FunDep
import HybridPredicate -- (HPhrase)
import Label (NoDuplicates, IsDisjoint, Subset, Subtract, SymAsSet)
import Predicate ((:&), DefVI, EvalEnvRow, EvalRowType, FTV,
                  HasCols, LJDI, ReplacePredicate, Simplify,
                  SPhrase, TypesBool, Vars)
import RowType (Env, Project, ProjectEnv, JoinEnv, RecoverEnv,
                RemoveEnv, OverlappingJoin, VarsEnv)
import SortedRecords (Revisable, RevisableFd, RecordsSet, rows)
import Tables (DisjointTables, RecoverTables, Tables)

import qualified DynamicPredicate as DP
import qualified Types as T
import qualified Predicate as P
import qualified RowType as R
import qualified SortedRecords as RT


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

type LensCommon ts rt p fds =
  (Affected fds rt,
   Revisable (TopologicalSort fds) rt rt,
   RecoverTables ts,
   RecoverEnv rt,
   Recoverable (VarsEnv rt) [String],
   LookupMap rt,
   FromRow (R.Row rt),
   ToDynamic rt,
   NoDuplicates rt
   )

type Lensable ts rt p fds fdsnew =
  (fdsnew ~ SplitFDs fds,
   p ~ DefaultPredicate,
   LensCommon ts rt p fdsnew,
   Project (TableKey rt fdsnew) rt,
   ToDynamic (ProjectEnv (TableKey rt fdsnew) rt),
   Recoverable (VarsEnv (ProjectEnv (TableKey rt fdsnew) rt)) [String],
   Project (UpdateColumns rt fdsnew) rt,
   ToDynamic (ProjectEnv (UpdateColumns rt fdsnew) rt),
   Recoverable (VarsEnv (ProjectEnv (UpdateColumns rt fdsnew) rt)) [String])

type JoinImplConstraints ts1 rt1 p1 fds1 ts2 rt2 p2 fds2 rtnew joincols =
  (LensCommon ts1 rt1 p1 fds1,
   LensCommon ts2 rt2 p2 fds2,
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

type Joinable ts1 rt1 p1 fds1 ts2 rt2 p2 fds2 rtnew joincols =
  (rtnew ~ JoinEnv rt1 rt2,
   joincols ~ R.InterCols rt1 rt2,
   DisjointTables ts1 ts2,
   OverlappingJoin rt1 rt2,
   IgnoresOutputs p1 fds1, IgnoresOutputs p2 fds2,
   Subset (VarsEnv rt2) (TransClosure joincols fds2),
   InTreeForm fds1, InTreeForm fds2,
   JoinImplConstraints ts1 rt1 p1 fds1 ts2 rt2 p2 fds2 rtnew joincols)

type SelectImplConstraints rt p pred fds =
  (Affected fds rt, LookupMap rt, Revisable (TopologicalSort fds) rt rt,
   FromRow (R.Row rt),
   R.Fields rt)

type Selectable rt p pred fds pnew =
  (pnew ~ Simplify (p :& pred),
   TypesBool rt p,
   IgnoresOutputs pred fds,
   InTreeForm fds,
   SelectImplConstraints rt p pred fds)

type DropImplConstraints env key rt pred fds rtnew =
  (RT.Joinable rtnew (EvalRowType env) rt,
   RecoverEnv rt,
   EvalEnvRow env, FromRow (R.Row rtnew),
   RevisableFd (key --> Vars env) rt (R.ProjectEnv (key :++ P.Vars env) rt),
   Recoverable (SymAsSet key) [String],
   Project (SymAsSet key) rtnew,
   Affected '[key --> Vars env] rtnew,
   FromRow (R.Row (ProjectEnv (key :++ P.Vars env) rt)),
   RecoverEnv (ProjectEnv (key :++ P.Vars env) rt))

type Droppable env key rt pred fds rtnew prednew fdsnew =
  (rtnew ~ RemoveEnv (Vars env) rt,
   prednew ~ Simplify (ReplacePredicate env pred),
   fdsnew ~ DropColumn (Vars env) fds,
   HasCols env rt, LJDI (Vars env) pred, DefVI env pred,
   DropImplConstraints env key rt pred fds rtnew)

type Debuggable rt =
  (R.Fields rt)

data Lens (tables :: Tables) (rt :: Env) (p :: SPhrase) (fds :: [FunDep]) where
  Prim :: Lensable '[table] rt p fds fdsnew => Lens '[table] rt p fdsnew
  Debug :: Debuggable rt => Lens ts rt p fds -> Lens ts rt p fds
  Join :: Joinable ts1 rt1 p1 fds1 ts2 rt2 p2 fds2 rtnew joincols =>
    Lens ts1 rt1 p1 fds1 ->
    Lens ts2 rt2 p2 fds2 ->
    Lens (ts1 :++ ts2) rtnew (Simplify (p1 :& p2)) (SplitFDs (fds1 :++ fds2))
  Select :: Selectable rt p pred fds pnew =>
    HPhrase p ->
    Lens ts rt pred fds ->
    Lens ts rt pnew fds
  Drop ::
    Droppable env (key :: [Symbol]) rt pred fds rtnew prednew fdsnew =>
    Proxy key ->
    Proxy env ->
    Lens ts rt pred fds ->
    Lens ts rtnew prednew fdsnew

type family RowType l :: Env where
  RowType (Lens ts rt p fds) = rt

data FromRowHack (rt :: Env) where
  Hack :: FromRow (R.Row rt) => FromRowHack rt

lrows :: (vars ~ R.TupleType rt, R.ToRow rt vars) =>
  Lens ts rt p fds -> [vars] -> RecordsSet rt
lrows (l :: Lens ts rt p fds) vars = rows @rt vars

lensToFromRowHack :: Lens ts rt p fds -> FromRowHack rt
lensToFromRowHack Prim = Hack
lensToFromRowHack (Debug l) = lensToFromRowHack l
lensToFromRowHack (Select _ _) = Hack
lensToFromRowHack (Drop _ _ _) = Hack
lensToFromRowHack (Join _ _) = Hack

prim :: forall table rt fds p fdsnew. Lensable '[table] rt p fds fdsnew => Lens '[table] rt p fdsnew
prim = Prim @table @rt @p @fds @fdsnew

select :: forall p ts rt pred fds pnew. Selectable rt p pred fds pnew =>
  HPhrase p -> Lens ts rt pred fds -> Lens ts rt (Simplify (p :& pred)) fds
select pred l = Select @rt @p @pred @fds @pnew pred l

dropl :: forall env (key :: [Symbol]) rt pred ts fds rtnew prednew fdsnew. (Droppable env key rt pred fds rtnew prednew fdsnew, RecoverEnv rt ) =>
  Lens ts rt pred fds -> Lens ts rtnew prednew fdsnew
dropl l = Drop @env @key @rt @pred @fds @rtnew @prednew @fdsnew @ts Proxy Proxy l

join :: Joinable ts1 rt1 p1 fds1 ts2 rt2 p2 fds2 rtnew joincols =>
    Lens ts1 rt1 p1 fds1 ->
    Lens ts2 rt2 p2 fds2 ->
    Lens (ts1 :++ ts2) rtnew (Simplify (p1 :& p2)) (SplitFDs (fds1 :++ fds2))
join l1 l2 = Join l1 l2

lens1 = prim @"test1" @'[ '("A", Int), '("B", String)] @'[ '["A"] --> '["B"]]
lens2 = select (var @"A" !> i @30) lens1
lens3 = dropl @'[ '("B", 'P.String "test")] @'["A"] lens2
