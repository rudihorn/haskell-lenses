{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving #-}

module Lens where

import Label
import Data.Type.Set
import Predicate
import FunDep
import qualified Types

type family IsIgnoresOutputs (phrase :: Phrase) (fds :: [FunDep]) :: Bool where
  IsIgnoresOutputs p fds = IsDisjoint (FTV p) (Outputs fds)

type IgnoresOutputs p fds = IsIgnoresOutputs p fds ~ 'True

data Lens (rt :: Env) (p :: Phrase) (fds :: [FunDep]) where
  Prim :: Proxy rt -> Proxy fds -> Lens rt (Predicate.B 'True) (SplitFDs fds)
  Join :: (IgnoresOutputs p1 fds1, IgnoresOutputs p2 fds2, InTreeForm fds1, InTreeForm fds2) =>
    Lens rt1 p1 fds1 ->
    Lens rt2 p2 fds2 ->
    Lens rt1 (Simplify (p1 :& p2)) (SplitFDs (fds1 :++ fds2))
  Select :: (TypesBool rt p, IgnoresOutputs pred fds, InTreeForm fds) =>
    Proxy p ->
    Lens rt pred fds ->
    Lens rt (Simplify (p :& pred)) fds
  Drop ::
    (HasCols env rt, LJDI (Vars env) pred, DefVI env pred) =>
    Proxy env ->
    Lens rt pred fds ->
    Lens (RemoveEnv (Vars env) rt) (Simplify (ReplacePredicate env pred)) fds


lens1 = Prim (Proxy :: Proxy '[ '("A", 'Types.Int)]) (Proxy :: Proxy '[])
lens2 = Select (Proxy :: Proxy (V "A" :> I 30)) lens1
lens3 = Drop (Proxy :: Proxy '[ '("A", 'Int 40)]) lens2
