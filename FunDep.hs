{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving #-}

module FunDep where

import GHC.TypeLits
import GHC.TypeNats
import Data.Type.Bool
import Data.Type.Set
import Data.Kind
import Label

data FunDep where
  FunDep :: [Symbol] -> [Symbol] -> FunDep

type family (-->) (left :: [Symbol]) (right :: [Symbol]) :: FunDep where
  xs --> ys = ('FunDep (SymAsSet xs) (SymAsSet ys) :: FunDep)

class FunDepKnown f where
  left :: f -> [String]
  right :: f -> [String]

--instance (LabListKnown (LabList l), LabListKnown (LabList r)) => FunDepKnown (FunDep ('LabList :: LabList l) ('LabList :: LabList r)) where
--  left _ = labListVal (LabList :: LabList l)
--  right _ = labListVal (LabList :: LabList r)

-- instance FunDepKnown (FunDep l r) => Show (FunDep l r) where
--  show f = ppList " " (left f) ++ " --> " ++ ppList " " (right f)

type Fd1 = '["A", "B"] --> '["C"]
type Fd2 = '["C"] --> '["D", "E"]
type Fd3 = '["F"] --> '["G"]
type Fd4 = '["D"] --> '["H"]
type Fd5 = '["D"] --> '["I"]
type Fd6 = '["B"] --> '["H"]
type Fd7 = '["C"] --> '["D"]

type Fds1 = '[Fd1, Fd2, Fd3, Fd4]
type Fds2 = '[Fd1, Fd2, Fd3, Fd4, Fd5]
type Fds3 = '[Fd1, Fd2, Fd3, Fd4, Fd6]
type Fds4 = '[Fd1, Fd7, Fd3, Fd4]

data FunDepList :: [k] -> * where
  FunDepList :: FunDepList fds

type family Left (f :: FunDep) :: [Symbol] where
  Left ('FunDep left _) = left

type family Right (f :: FunDep) :: [Symbol] where
  Right ('FunDep _ right) = right

type family Rights (f :: [FunDep]) :: [[Symbol]] where
  Rights '[] = '[]
  Rights (x ': xs) = Right x ': Rights xs

type family Lefts (f :: [FunDep]) :: [[Symbol]] where
  Lefts '[] = '[]
  Lefts (x ': xs) = Left x ': Lefts xs

-- from label list to fundep list
type family Closure (from :: [Symbol]) (to :: [FunDep]) :: [Symbol] where
  Closure fr '[] = fr
  Closure fr (f ': fds) = If (IsSubset (Left f) fr) (SymUnion (Right f) (Closure fr fds)) (Closure fr fds)

type family TransClosure (from :: [Symbol]) (to :: [FunDep]) :: [Symbol] where
  TransClosure fr fds = TransClosureF fr fds (Len fds)

type family TransClosureF (from :: [Symbol]) (to :: [FunDep]) fuel :: [Symbol] where
  TransClosureF fr fds 0 = fr
  TransClosureF fr fds n = (TransClosureF (Closure fr fds) fds (n-1))

type family Outputs (fds :: [FunDep]) where
  Outputs '[] = '[]
  Outputs (fd ': fds) = (SetSubtract (Right fd) (Left fd)) :++ Outputs fds

type family IsInTreeForm (fds :: [FunDep]) where
  IsInTreeForm fds =
    AllDisjoint (Rights fds) && AllDisjoint (SLAsSet (Rights fds :++ Lefts fds)) && IsAcyclic fds

type InTreeForm fds = IsInTreeForm fds ~ 'True

-- Cycle checks

type family StartingPoints (lefts :: [[Symbol]]) (rights :: [[Symbol]]) :: [[Symbol]] where
  StartingPoints '[] _ = '[]
  StartingPoints (x ': xs) rights = If (DisjointFromAll x rights) (x ': StartingPoints xs rights) (StartingPoints xs rights)

type family FollowRes (isel :: Bool) (from :: [[Symbol]]) (fd :: FunDep) (sub :: ([[Symbol]], [FunDep])) :: ([[Symbol]], [FunDep]) where
  FollowRes 'True from fd '(visited, fds) = '(Right fd ': visited, fds)
  FollowRes 'False from fd '(visited, fds) = '(visited, fd ': fds)

type family Follow (from :: [[Symbol]]) (fds :: [FunDep]) :: ([[Symbol]], [FunDep]) where
  Follow from '[] = '(from, '[])
  Follow from (fd ': fds) = FollowRes (IsElement (Left fd) from) from fd (Follow from fds)

type family IsAcyclicEx (res :: ([[Symbol]], [FunDep])) (fuel :: Nat) :: Bool where
  IsAcyclicEx '(syms, '[]) _ = AllDisjoint syms
  IsAcyclicEx _ 0 = 'False
  IsAcyclicEx '(syms, fds) n = IsAcyclicEx (Follow syms fds) (n-1)

type family IsAcyclic (fds :: [FunDep]) :: Bool where
  IsAcyclic fds = IsAcyclicEx '(StartingPoints (Lefts fds) (Rights fds), fds) (Len fds)

-- FDS sanitation

type family RightSplit (right :: [Symbol]) (lefts :: [[Symbol]]) :: [[Symbol]] where
  RightSplit '[] _ = '[]
  RightSplit r '[] = '[r]
  RightSplit r (x ': xs) = If (IsSubset x r) (x ': RightSplit (SetSubtract r x) xs) (RightSplit r xs)

type family MakeFDs (left :: [Symbol]) (rights :: [[Symbol]]) :: [FunDep] where
  MakeFDs _ '[] = '[]
  MakeFDs left (r ': rs) = 'FunDep left r ': MakeFDs left rs

type family FDSRightSplitEx (fds :: [FunDep]) (lefts :: [[Symbol]]) :: [FunDep] where
  FDSRightSplitEx '[] _ = '[]
  FDSRightSplitEx (fd ': fds) lefts =
    MakeFDs (Left fd) (RightSplit (Right fd) lefts) :++ FDSRightSplitEx fds lefts

type family SplitFDs (fds :: [FunDep]) :: [FunDep] where
  SplitFDs fds = FDSRightSplitEx fds (Lefts fds)
