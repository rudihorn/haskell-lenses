{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications #-}

module Lens where

import Common
import Tables
import Label
import Data.Type.Set
import Predicate
import FunDep
import RowType
import qualified Types as T
import qualified Value as V
import qualified DynamicPredicate as DP

type family IsIgnoresOutputs (phrase :: SPhrase) (fds :: [FunDep]) :: Bool where
  IsIgnoresOutputs p fds = IsDisjoint (FTV p) (Outputs fds)

type IgnoresOutputs p fds = IsIgnoresOutputs p fds ~ 'True

type DefaultPredicate = Predicate.B 'True

type Lensable rt fds = NoDuplicates rt

type Joinable ts1 rt1 p1 fds1 ts2 rt2 p2 fds2 = (DisjointTables ts1 ts2, OverlappingJoin rt1 rt2, IgnoresOutputs p1 fds1, IgnoresOutputs p2 fds2, InTreeForm fds1, InTreeForm fds2, RecoverEnv rt1, RecoverEnv rt2, RecoverTables ts1, RecoverTables ts2, Recoverable p1 DP.Phrase, Recoverable p2 DP.Phrase)

type Selectable rt p pred fds = (TypesBool rt p, IgnoresOutputs pred fds, InTreeForm fds, Recoverable p DP.Phrase, Recoverable pred DP.Phrase)

type Droppable env rt pred = (HasCols env rt, LJDI (Vars env) pred, DefVI env pred, RecoverEnv rt, Recoverable pred DP.Phrase)

data Lens (tables :: Tables) (rt :: Env) (p :: SPhrase) (fds :: [FunDep]) where
  Prim :: Lensable rt fds => Lens '[table] rt DefaultPredicate (SplitFDs fds)
  Join :: Joinable ts1 rt1 p1 fds1 ts2 rt2 p2 fds2 =>
    Lens ts1 rt1 p1 fds1 ->
    Lens ts2 rt2 p2 fds2 ->
    Lens (ts1 :++ ts2) (JoinRowTypes rt1 rt2) (Simplify (p1 :& p2)) (SplitFDs (fds1 :++ fds2))
  Select :: Selectable rt p pred fds =>
    Proxy p ->
    Lens ts rt pred fds ->
    Lens ts rt (Simplify (p :& pred)) fds
  Drop ::
    (Droppable env rt pred) =>
    Lens ts rt pred fds ->
    Lens ts (RemoveEnv (Vars env) rt) (Simplify (ReplacePredicate env pred)) fds

prim :: forall table rt fds. Lensable rt fds => Lens '[table] rt DefaultPredicate (SplitFDs fds)
prim = Prim @rt @fds @table

select :: forall p ts rt pred fds. Selectable rt p pred fds =>
  Lens ts rt pred fds -> Lens ts rt (Simplify (p :& pred)) fds
select l = Select @rt @p @pred @fds Proxy l

dropl :: forall env rt pred ts fds. (Droppable env rt pred, RecoverEnv rt ) =>
  Lens ts rt pred fds -> Lens ts (RemoveEnv (Vars env) rt) (Simplify (ReplacePredicate env pred)) fds
dropl l = Drop @env @rt @pred @ts @fds l

join :: Joinable ts1 rt1 p1 fds1 ts2 rt2 p2 fds2 =>
    Lens ts1 rt1 p1 fds1 ->
    Lens ts2 rt2 p2 fds2 ->
    Lens (ts1 :++ ts2) (JoinRowTypes rt1 rt2) (Simplify (p1 :& p2)) (SplitFDs (fds1 :++ fds2))
join l1 l2 = Join l1 l2

lens1 = prim @"test1" @'[ '("A", 'T.Int), '("B", 'T.String)] @'[ '["A"] --> '["B"]]
lens2 = select @(V "A" :> I 30) lens1
lens3 = dropl @'[ '("A", 'Int 40)] lens2

-- Bohanonn et al. PODS 2016 examples
albums = prim @"Albums" @'[ '("Album", 'T.String), '("Quantity", 'T.Int)]
  @'[ '["Album"] --> '["Quantity"]]

tracks = prim @"Tracks" @'[ '("Track", 'T.String), '("Date", 'T.Int), '("Rating", 'T.Int), '("Album", 'T.String)]
  @'[ '["Track"] --> '["Date", "Rating"]]

tracks1 = join albums tracks

tracks2 = dropl @'[ '("Track", 'String "unknown")] tracks1

tracks3 = select @(V "Quantity" :> I 2) tracks2
