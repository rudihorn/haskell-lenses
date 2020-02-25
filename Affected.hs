{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications #-}

module Affected where

import Data.Type.Set (Proxy(..))
import qualified Data.Set as Set

import Common
import DynamicPredicate (DPhrase)
import FunDep (FunDep(..), Left)
import RowType (Env)
import SortedRecords (project, RecordsSet)

import qualified DynamicPredicate as DP
import qualified Predicate as P
import qualified RowType as R
import qualified Value as V


toDPValue :: (V.Value t) -> DP.Value
toDPValue (V.String s) = DP.String s
toDPValue (V.Int s) = DP.Int s
toDPValue (V.Bool s) = DP.Bool s

class ToDynamic rt where
  toDynamic :: R.Row rt -> [DP.Value]

instance ToDynamic '[] where
  toDynamic _ = []

instance ToDynamic xs => ToDynamic (x ': xs) where
  toDynamic (R.Cons v rw) = toDPValue v : toDynamic rw

toDPList :: ToDynamic rt => RecordsSet rt -> [[DP.Value]]
toDPList = map toDynamic . Set.toList


class Affected (fds :: [FunDep]) (rt :: Env) where
  affected :: RecordsSet rt -> DPhrase

instance Affected '[] rt where
  affected _ = P.Constant (DP.Bool True)

instance (Recoverable (Left fd) [String], R.Project (Left fd) rt, Affected fds rt, ToDynamic (R.ProjectEnv (Left fd) rt)) =>
  Affected (fd ': fds) rt where
  affected rt = DP.conjunction [
    P.In (recover @(Left fd) Proxy) (toDPList $ project @(Left fd) rt),
    affected @fds rt]
