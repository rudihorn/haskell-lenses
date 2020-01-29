{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             TypeApplications #-}

module DynamicPredicate where

import Common
import Data.Type.Set
import GHC.TypeLits
import qualified Types
import RowType
import qualified Predicate as P

data Value where
  Bool :: Bool -> Value
  Int :: Int -> Value
  String :: String -> Value

-- data Predicate (r :: Env) where
--  Constant :: Value -> Predicate '[]
--  Var :: (KnownSymbol s, Recoverable t Types.Type) => Proxy '(s,t) -> Predicate '[ '(s, t)]
--  InfixAppl :: Operator -> Predicate r1 -> Predicate r2 -> Predicate ()

type Phrase = P.Phrase String Value

instance Recoverable b Bool => Recoverable ('P.Bool b) Value where
  recover Proxy = Bool (recover (Proxy :: Proxy b))

instance KnownNat i => Recoverable ('P.Int i) Value where
  recover Proxy = Int (fromIntegral $ natVal (Proxy :: Proxy i))

instance KnownSymbol s => Recoverable ('P.String s) Value where
  recover Proxy = String (symbolVal (Proxy :: Proxy s))



-- Phrase

instance Recoverable v Value => Recoverable ('P.Constant v) Phrase where
  recover Proxy = P.Constant (recover (Proxy :: Proxy v))

instance KnownSymbol v => Recoverable ('P.Var v) Phrase where
  recover Proxy = P.Var (symbolVal (Proxy :: Proxy v))

instance (Recoverable p1 Phrase, Recoverable p2 Phrase, Recoverable op P.Operator) => Recoverable ('P.InfixAppl op p1 p2) Phrase where
  recover Proxy = P.InfixAppl (recover @op Proxy) (recover @p1 Proxy) (recover @p2 Proxy)

instance (Recoverable p Phrase, Recoverable op P.UnaryOperator) => Recoverable ('P.UnaryAppl op p) Phrase where
  recover Proxy = P.UnaryAppl (recover @op Proxy) (recover @p Proxy)

simplify :: Phrase -> Phrase
simplify (P.InfixAppl (P.LogicalAnd) (P.Constant (Bool True)) p2) = p2
simplify (P.InfixAppl (P.LogicalAnd) (P.Constant (Bool False)) _) = P.Constant (Bool False)
simplify (P.InfixAppl (P.LogicalAnd) p1 (P.Constant (Bool True))) = p1
simplify (P.InfixAppl (P.LogicalAnd) _ (P.Constant (Bool False))) = P.Constant (Bool False)
simplify p = p
