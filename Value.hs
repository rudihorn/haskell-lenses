{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             TypeApplications #-}

module Value where

import GHC.TypeLits
import Data.Type.Set (Proxy(..))

import Common

import qualified Types as T

data Value (typ :: T.Type) where
  String :: String -> Value 'T.String
  Symbol :: Symbol -> Value 'T.String
  Int :: Int -> Value 'T.Int
  Bool :: Bool -> Value 'T.Bool

valof :: Value t -> (T.HaskellType t)
valof (String s) = s
valof (Symbol _) = "<error>"
valof (Int i) = i
valof (Bool b) = b

instance Show (Value 'T.String) where
  show (String s) = show s
  show (Symbol _) = "<error>"

instance Show (Value 'T.Int) where
  show (Int s) = show s

instance Show (Value 'T.Bool) where
  show (Bool s) = show s

class MakeValue t where
  make :: t -> Value (T.LensType t)

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

instance KnownSymbol s => Recoverable ('Symbol s) (Value 'T.String) where
  recover Proxy = String (symbolVal @s Proxy)
