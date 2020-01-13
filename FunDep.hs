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

type Fds1 = '[Fd1, Fd2, Fd3, Fd4]

data FunDepList :: [k] -> * where
  FunDepList :: FunDepList fds

type family Left (f :: FunDep) :: [Symbol] where
  Left ('FunDep left _) = left

type family Right (f :: FunDep) :: [Symbol] where
  Right ('FunDep _ right) = right

-- from label list to fundep list
type family Closure (from :: [Symbol]) (to :: [FunDep]) :: [Symbol] where
  Closure fr '[] = fr
  Closure fr (f ': fds) = If (IsSubset (Left f) fr) (SymUnion (Right f) (Closure fr fds)) (Closure fr fds)

type family TransClosure (from :: [Symbol]) (to :: [FunDep]) :: [Symbol] where
  TransClosure fr fds = TransClosureF fr fds (Len fds)

type family TransClosureF (from :: [Symbol]) (to :: [FunDep]) fuel :: [Symbol] where
  TransClosureF fr fds 0 = fr
  TransClosureF fr fds n = (TransClosureF (Closure fr fds) fds (n-1))
