{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             TypeApplications
              #-}

module Common where

import Data.Maybe
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

instance Recoverable 'Nothing (Maybe p) where
  recover Proxy = Nothing

instance Recoverable p q => Recoverable ('Just p) (Maybe q) where
  recover Proxy = Just $ (recover @p @q Proxy)

instance Recoverable '[] [a] where
  recover Proxy = []

instance (Recoverable x a, Recoverable xs [a]) => Recoverable (x ': xs) [a] where
  recover Proxy = recover @x @a Proxy : recover @xs Proxy

instance (Recoverable p q, Recoverable r s) => Recoverable '(p, r) (q, s) where
  recover Proxy = (recover @p @q Proxy, recover @r @s Proxy)
