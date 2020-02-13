{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             TypeApplications #-}

module Value where

import GHC.TypeLits
import qualified Types

data Value (typ :: Types.Type) where
  String :: String -> Value 'Types.String
  Symbol :: Symbol -> Value 'Types.String
  Int :: Int -> Value 'Types.Int
  Bool :: Bool -> Value 'Types.Bool

valof :: Value t -> (Types.HaskellType t)
valof (String s) = s
valof (Symbol _) = "<error>"
valof (Int i) = i
valof (Bool b) = b

instance Show (Value 'Types.String) where
  show (String s) = show s
  show (Symbol _) = "<error>"

instance Show (Value 'Types.Int) where
  show (Int s) = show s

instance Show (Value 'Types.Bool) where
  show (Bool s) = show s

class MakeValue t where
  make :: t -> Value (Types.LensType t)

instance MakeValue String where
  make s = String s

instance MakeValue Bool where
  make s = Bool s

instance MakeValue Int where
  make s = Int s

instance Eq (Value t) where
  String s == String s' = s == s'
  Int i == Int i' = i == i'
  Bool b == Bool b' = b == b'
  _ == _ = False

instance Ord (Value t) where
  compare (String s) (String s') = compare s s'
  compare (Int i) (Int i') = compare i i'
  compare (Bool b) (Bool b') = compare b b'
  compare _ _ = LT
