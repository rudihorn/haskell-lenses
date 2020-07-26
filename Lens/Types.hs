{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving #-}

module Lens.Types where

import Common
import Data.Type.Set

data Type where
  String :: Type
  Bool :: Type
  Int :: Type

type family HaskellType (t :: Type) :: * where
  HaskellType 'String = String
  HaskellType 'Bool = Bool
  HaskellType 'Int = Int

type family LensType (t :: *) :: Type where
  LensType String = 'String
  LensType Bool = 'Bool
  LensType Int = 'Int

instance Show Type where
  show String = "string"
  show Bool = "bool"
  show Int = "int"

instance Recoverable (String) Type where
  recover Proxy = String

instance Recoverable (Bool) Type where
  recover Proxy = Bool

instance Recoverable (Int) Type where
  recover Proxy = Int

recover_type :: Recoverable i Type => (Proxy i) -> Type
recover_type i = recover i
