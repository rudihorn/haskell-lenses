{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             TypeApplications, AllowAmbiguousTypes, OverloadedLabels #-}


module Lens.Predicate.Hybrid where

import Data.Type.Set
import GHC.TypeLits
import GHC.OverloadedLabels (IsLabel(..))
import System.IO.Unsafe

import Common
import Lens.Predicate.Base

import qualified Lens.Predicate.Dynamic as DP
import qualified Lens.Predicate.Base as P
import qualified Lens.Predicate.Precedence as QP

type DPhrase = DP.Phrase

data HPhrase (p :: SPhrase) where
  HPred :: DPhrase -> HPhrase p

of_static :: forall (p :: SPhrase). Recoverable p DPhrase => HPhrase p
of_static = HPred @p $ recover @p Proxy

erased :: forall rt ret (p :: SPhrase). (P.Typ rt p ~ 'Just ret) => HPhrase p -> HPhrase ('P.Erased rt ret)
erased (HPred p) = HPred p

instance forall v p. (KnownSymbol v, p ~ 'P.Var v) => IsLabel v (HPhrase p) where
  fromLabel = of_static @('P.Var v)

var :: forall v. KnownSymbol v => HPhrase ('P.Var v)
var = of_static @('P.Var v)

(#>) :: forall p1 p2. HPhrase p1 -> HPhrase p2 -> HPhrase (p1 :> p2)
(HPred p1) #> (HPred p2) = HPred $ P.InfixAppl P.GreaterThan p1 p2

(#<) :: forall p1 p2. HPhrase p1 -> HPhrase p2 -> HPhrase (p1 :< p2)
(HPred p1) #< (HPred p2) = HPred $ P.InfixAppl P.LessThan p1 p2

(#&) :: forall p1 p2. HPhrase p1 -> HPhrase p2 -> HPhrase (p1 :& p2)
(HPred p1) #& (HPred p2) = HPred $ P.InfixAppl P.LogicalAnd p1 p2

(#|) :: forall p1 p2. HPhrase p1 -> HPhrase p2 -> HPhrase (p1 :| p2)
(HPred p1) #| (HPred p2) = HPred $ P.InfixAppl P.LogicalAnd p1 p2

(#=) :: forall p1 p2. HPhrase p1 -> HPhrase p2 -> HPhrase (p1 := p2)
(HPred p1) #= (HPred p2) = HPred $ P.InfixAppl P.Equal p1 p2

(#+) :: forall p1 p2. HPhrase p1 -> HPhrase p2 -> HPhrase (p1 :+ p2)
(HPred p1) #+ (HPred p2) = HPred $ P.InfixAppl P.Plus p1 p2

(#-) :: forall p. HPhrase p -> HPhrase ('P.UnaryAppl 'P.Negate p)
(#-) (HPred p) = HPred $ P.UnaryAppl P.Negate p

neg :: forall p. HPhrase p -> HPhrase ('P.UnaryAppl 'P.UnaryMinus p)
neg (HPred p) = HPred $ P.UnaryAppl P.UnaryMinus p

i :: forall v. KnownNat v => HPhrase ('P.Constant ('P.Int v))
i = of_static @('P.Constant ('P.Int v))

s :: forall v. KnownSymbol v => HPhrase ('P.Constant ('P.String v))
s = of_static @('P.Constant ('P.String v))

b :: forall v. Recoverable v Bool => HPhrase ('P.Constant ('P.Bool v))
b = of_static @('P.Constant ('P.Bool v))

di :: Int -> HPhrase ('P.Erased '[] Int)
di v = HPred (P.Constant $ DP.Int v)

ds :: String -> HPhrase ('P.Erased '[] String)
ds v = HPred (P.Constant $ DP.String v)

db :: Bool -> HPhrase ('P.Erased '[] Bool)
db v = HPred (P.Constant $ DP.Bool v)

ifthen :: forall pcond pthen pelse. HPhrase pcond -> HPhrase pthen -> HPhrase pelse ->
  HPhrase (P.IfThen pcond pthen pelse)
ifthen (HPred pcond) (HPred pthen) (HPred pelse) =
  HPred $ P.Case (Just pcond) [(P.Constant $ DP.Bool True, pthen)] pelse

instance Show (HPhrase pred) where
  show (HPred p) = show $ unsafePerformIO $ DP.print_query p QP.first

-- dynamic @Env1 @'T.Int (ifthen (var @"A" !> var @"B") (di 55) (i @10))
