{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving
              #-}

module Common where

import Data.Type.Set
import GHC.TypeLits

data Result where
  Ok :: Result
  Fail :: ErrorMessage -> Result

type family UnpackResult res where
  UnpackResult 'Ok = ()
  UnpackResult ('Fail msg) = TypeError msg

type family OkOrError cond err where
  OkOrError 'True _ = 'True ~ 'True
  OkOrError 'False err = TypeError err

class Recoverable i t where
  recover :: Proxy i -> t

instance Recoverable 'True Bool where
  recover Proxy = True

instance Recoverable 'False Bool where
  recover Proxy = False

instance KnownSymbol s => Recoverable (s :: Symbol) String where
  recover p = symbolVal p

type family UnpackMaybe (x :: Maybe t) :: t where
  UnpackMaybe ('Just x) = x
