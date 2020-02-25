{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             TypeApplications, OverloadedStrings #-}

module CompilePredicate where

import GHC.TypeLits
import Data.Type.Set (Proxy(..))
import Data.Map.Strict ((!))

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import DynamicPredicate (DPhrase, Value)
import RowType (Row)

import qualified DynamicPredicate as DP
import qualified Predicate as P
import qualified RowType as R
import qualified Value as V

fromRValue :: V.Value t -> Value
fromRValue (V.Int i) = DP.Int i
fromRValue (V.String s) = DP.String s
fromRValue (V.Bool b) = DP.Bool b

class LookupMap rt where
  lookupMap :: Map.Map String (Row rt -> Value)

instance LookupMap '[] where
 lookupMap = Map.empty

instance (KnownSymbol k, LookupMap rt) => LookupMap ('(k, t) ': rt) where
  lookupMap = Map.insert (symbolVal (Proxy :: Proxy k)) thisF extMap where
    thisF :: Row ('(k, t) ': rt) -> Value
    thisF (R.Cons v _) = fromRValue v
    extMap = Map.map upd $ lookupMap @rt
    upd :: (Row rt -> Value) -> (Row ('(k, t) ': rt) -> Value)
    upd f (R.Cons _ r) = f r

log_and :: Value -> Value -> Value
log_and (DP.Bool True) (DP.Bool True) = DP.Bool True
log_and (DP.Bool _) (DP.Bool _) = DP.Bool False

log_or :: Value -> Value -> Value
log_or (DP.Bool False) (DP.Bool False) = DP.Bool False
log_or (DP.Bool _) (DP.Bool _) = DP.Bool True

cmp :: Ordering -> Value -> Value -> Value
cmp o (DP.Bool b1) (DP.Bool b2) = DP.Bool (compare b1 b2 == o)
cmp o (DP.String s1) (DP.String s2) = DP.Bool (compare s1 s2 == o)
cmp o (DP.Int i1) (DP.Int i2) = DP.Bool (compare i1 i2 == o)

plus :: Value -> Value -> Value
plus (DP.Int i1) (DP.Int i2) = DP.Int $ i1 + i2

infix_appl :: P.Operator -> Value -> Value -> Value
infix_appl P.LessThan = cmp LT
infix_appl P.GreaterThan = cmp GT
infix_appl P.Equal = cmp EQ
infix_appl P.LogicalAnd = log_and
infix_appl P.LogicalOr = log_or
infix_appl P.Plus = plus

unary_appl :: P.UnaryOperator -> Value -> Value
unary_appl (P.UnaryMinus) (DP.Int i) = DP.Int $ -i
unary_appl (P.Negate) (DP.Bool b) = DP.Bool $ not b

compile :: forall rt. LookupMap rt => DPhrase -> (Row rt -> Value)
compile (P.Constant v) = \ _ ->  v
compile (P.Var v) = lookupMap @rt ! v
compile (P.InfixAppl op p1 p2) = \r -> fop (f1 r) (f2 r) where
  fop = infix_appl op
  f1 = compile p1
  f2 = compile p2
compile (P.UnaryAppl op p) = \r -> fop (f r) where
  fop = unary_appl op
  f = compile p
compile (P.In ids vs) = (\r -> DP.Bool $ Set.member (fval r) valset) where
  lookups = map (\i -> lookupMap @rt ! i) ids
  fval = (\r -> map (\v -> v r) lookups)
  valset = Set.fromList vs
compile (P.Case p cases other) =
  (\r ->
    let match = f r in
    case List.find (\(p1, _) -> p1 r == match) fcases of
    Just (_, p2) -> p2 r
    Nothing -> fother r) where
  fdef = (\_ -> DP.Bool True)
  f = case p of
      Just jp -> compile jp
      Nothing -> fdef
  fcases = map (\(p1,p2) -> (compile @rt p1, compile @rt p2)) cases
  fother = compile other
