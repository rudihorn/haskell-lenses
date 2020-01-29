{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications #-}

module Tables where

import Common
import Label
import GHC.TypeLits
import Data.Type.Set

type Tables = [Symbol]

type DisjointTables ts1 ts2 = OkOrError (IsDisjoint ts1 ts2) ('Text "The tables are not disjoint.")

class RecoverTables t where
  recover_tables :: Proxy t -> [String]

instance RecoverTables '[] where
  recover_tables Proxy = []

instance (RecoverTables xs, KnownSymbol x) => RecoverTables (x ': xs) where
  recover_tables Proxy = symbolVal (Proxy :: Proxy x) : recover_tables (Proxy :: Proxy xs)
