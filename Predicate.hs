{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving #-}

module Predicate where

import GHC.TypeLits
import Data.List
import Data.Type.Set
import Data.Type.Bool
import Label
import qualified Types

data UnaryOperator where
  Negate :: UnaryOperator
  UnaryMinus :: UnaryOperator

data Operator where
  Plus :: Operator
  LogicalAnd :: Operator
  LogicalOr :: Operator
  GreaterThan :: Operator
  Equal :: Operator
  LessThan :: Operator

data Value where
  Bool :: Bool -> Value
  Int :: Nat -> Value
  String :: Symbol -> Value

data Phrase where
  Constant :: Value -> Phrase
  Var :: Symbol -> Phrase
  InfixAppl :: Operator -> Phrase -> Phrase -> Phrase
  UnaryAppl :: UnaryOperator -> Phrase -> Phrase
  In :: [Symbol] -> [[Value]] -> Phrase
  Case :: Maybe Phrase -> [(Phrase, Phrase)] -> Phrase

type family V (v :: Symbol) :: Phrase where
  V v = 'Var v

type family I (i :: Nat) :: Phrase where
  I v = 'Constant ('Int v)

type family S (i :: Symbol) :: Phrase where
  S v = 'Constant ('String v)

type family B (i :: Bool) :: Phrase where
  B v = 'Constant ('Bool v)

type family (:+) (p :: Phrase) (q :: Phrase) :: Phrase where
  p :+ q = 'InfixAppl 'Plus p q

type family (:&) (p :: Phrase) (q :: Phrase) :: Phrase where
  p :& q = 'InfixAppl 'LogicalAnd p q

type family (:|) (p :: Phrase) (q :: Phrase) :: Phrase where
 p :| q = 'InfixAppl 'LogicalOr p q

type family (:>) (p :: Phrase) (q :: Phrase) :: Phrase where
 p :> q = 'InfixAppl 'GreaterThan p q

type family (:=) (p :: Phrase) (q :: Phrase) :: Phrase where
 p :> q = 'InfixAppl 'Equal p q

type family (:<) (p :: Phrase) (q :: Phrase) :: Phrase where
 p :> q = 'InfixAppl 'LessThan p q

type Ph1 = I 0

type Ph2 = V "A"

type Ph3 = (V "A" :> I 99) :& (V "B" :| (V "C" :< I 30))

type Ph4 = (V "A" :> I 99) :& (V "B" :| (V "A" :< I 30))

type Env1 = '[ '("A", 'Types.Int), '("B", 'Types.Bool), '("C", 'Types.Int) ]

type family Neg (p :: Phrase) :: Phrase where
 Neg p = 'UnaryAppl 'UnaryMinus p

type family BNeg (p :: Phrase) :: Phrase where
 BNeg p = 'UnaryAppl 'Negate p

type family FTV (phrase :: Phrase) :: [Symbol] where
  FTV ('Constant _) = '[]
  FTV ('Var v) = '[v]
  FTV ('InfixAppl op p1 p2) = FTV p1 :++ FTV p2
  FTV ('UnaryAppl op p) = FTV p
  FTV ('In _ _) = '[]
  FTV ('Case 'Nothing ps) = '[]
  FTV ('Case ('Just p) ps) = FTV p

type Env = [(Symbol, Types.Type)]

type family VarsEnv (env :: Env) :: [Symbol] where
  VarsEnv '[] = '[]
  VarsEnv ( '(k, v) ': env) = k ': (VarsEnv env)

type family RemoveEnv (vars :: [Symbol]) (env :: Env) where
  RemoveEnv vs '[] = '[]
  RemoveEnv vs ( '(k, v) ': xs) = If (IsElement k vs) (RemoveEnv vs xs) ( '(k, v) ': RemoveEnv vs xs)


type family TypVal(c :: Value) :: Types.Type where
  TypVal ('Bool _) = 'Types.Bool
  TypVal ('Int _) = 'Types.Int
  TypVal ('String _) = 'Types.String

type family LookupVar (env :: Env) (v :: Symbol) :: Maybe Types.Type where
  LookupVar '[] _ = 'Nothing
  LookupVar ('(key,val) ': xs) key = 'Just val
  LookupVar (_ ': xs) key = LookupVar xs key

type family TypUnary (op :: UnaryOperator) (pt :: Maybe Types.Type) :: Maybe Types.Type where
  TypUnary 'Negate ('Just 'Types.Bool) = 'Just 'Types.Bool
  TypUnary 'UnaryMinus ('Just 'Types.Int) = 'Just 'Types.Int
  TypUnary _ _ = 'Nothing

type family TypCmp (pt1 :: Maybe Types.Type) (pt2 :: Maybe Types.Type) :: Maybe Types.Type where
  TypCmp 'Nothing 'Nothing = 'Nothing
  TypCmp a a = 'Just 'Types.Bool
  TypCmp _ _ = 'Nothing

type family TypInfix (op :: Operator) (pt1 :: Maybe Types.Type) (pt2 :: Maybe Types.Type) :: Maybe Types.Type where
  TypInfix 'Plus ('Just 'Types.Int) ('Just 'Types.Int) = 'Just 'Types.Int
  TypInfix 'LogicalAnd ('Just 'Types.Bool) ('Just 'Types.Bool) = 'Just 'Types.Bool
  TypInfix 'LogicalOr ('Just 'Types.Bool) ('Just 'Types.Bool) = 'Just 'Types.Bool
  TypInfix 'GreaterThan pt1 pt2 = TypCmp pt1 pt2
  TypInfix 'Equal pt1 pt2 = TypCmp pt1 pt2
  TypInfix 'LessThan pt1 pt2 = TypCmp pt1 pt2
  TypInfix _ _ _ = 'Nothing

type family Typ (env :: Env) (phrase :: Phrase) :: Maybe Types.Type where
  Typ _ ('Constant c) = 'Just (TypVal c)
  Typ env ('Var v) = LookupVar env v
  Typ env ('UnaryAppl op p) = TypUnary op (Typ env p)
  Typ env ('InfixAppl op p1 p2) = TypInfix op (Typ env p1) (Typ env p2)

type TypesBool env phr = Typ env phr ~ 'Just 'Types.Bool

type family IsLJDI (vs :: [Symbol]) (phrase :: Phrase) :: Bool where
  IsLJDI vs ('InfixAppl 'LogicalAnd p1 p2) = IsLJDI vs p1 && IsLJDI vs p2
  IsLJDI vs p = IsSubset (FTV p) vs || IsDisjoint (FTV p) vs

-- :t Proxy :: Proxy (IsLJDI Ph3 '["A"])
-- :t Proxy :: Proxy (IsLJDI Ph4 '["A"])

type LJDI vs p = IsLJDI vs p ~ 'True

type EvalEnv = [(Symbol,Value)]

type family Vars (env :: EvalEnv) :: [Symbol] where
  Vars '[] = '[]
  Vars ('(key,_) ': xs) = key ': Vars xs

type HasCols ev env = IsSubset (Vars ev) (VarsEnv env) ~ 'True

type EvalEnv1 = '[ '("A", 'Int 30), '("B", 'Bool 'True), '("C", 'Int 10) ]
type EvalEnv2 = '[ '("A", 'Int 100), '("B", 'Bool 'True), '("C", 'Int 10) ]

type family LookupEvalVar (env :: EvalEnv) (v :: Symbol) :: Maybe Value where
  LookupVar '[] _ = 'Nothing
  LookupVar ('(key,val) ': xs) key = 'Just val
  LookupVar (_ ': xs) key = LookupEvalVar xs key

type family IsCmp (o :: Ordering) (p :: Ordering) :: Maybe Value where
  IsCmp a a = 'Just ('Bool 'True)
  IsCmp _ _ = 'Just ('Bool 'False)

type family EvalCmp (o :: Ordering) (v1 :: Value) (v2 :: Value) :: Maybe Value where
  EvalCmp o ('Int v1) ('Int v2) = IsCmp (CmpNat v1 v2) o
  EvalCmp o ('String v1) ('String v2) = IsCmp (CmpSymbol v1 v2) o
  EvalCmp _ _ _ = 'Nothing

type family EvalInfix (op :: Operator) (v1 :: Maybe Value) (v2 :: Maybe Value) :: Maybe Value where
  EvalInfix 'Plus ('Just ('Int v1)) ('Just ('Int v2)) = 'Just ('Int (v1 + v2))
  EvalInfix 'LogicalAnd ('Just ('Bool v1)) ('Just ('Bool v2)) = 'Just ('Bool (v1 && v2))
  EvalInfix 'LogicalOr ('Just ('Bool v1)) ('Just ('Bool v2)) = 'Just ('Bool (v1 || v2))
  EvalInfix 'LessThan ('Just v1) ('Just v2) = EvalCmp 'LT v1 v2
  EvalInfix 'Equal ('Just v1) ('Just v2) = EvalCmp 'EQ v1 v2
  EvalInfix 'GreaterThan ('Just v1) ('Just v2) = EvalCmp 'GT v1 v2
  EvalInfix _ _ _ = 'Nothing

type family Eval (env :: EvalEnv) (phrase :: Phrase) :: Maybe Value where
  Eval _ ('Constant c) = 'Just c
  Eval env ('Var v) = LookupEvalVar env v
  Eval env ('InfixAppl op p1 p2) = EvalInfix op (Eval env p1) (Eval env p2)

-- Test with:
  -- :t Proxy :: Proxy (Eval EvalEnv1 Ph3)
  -- :t Proxy :: Proxy (Eval EvalEnv2 Ph3)
  -- :t Proxy :: Proxy (Eval EvalEnv2 Ph4)

type family UnpackTrue (v :: Maybe Value) :: Bool where
  UnpackTrue ('Just ('Bool 'True)) = 'True
  UnpackTrue _ = 'False

type family IsDefVIEx (subs :: Bool) (disj :: Bool) (env :: EvalEnv) (phrase :: Phrase) :: Bool where
  IsDefVIEx 'True _ env p = UnpackTrue (Eval env p)
  IsDefVIEx 'False 'True env p = 'True
  IsDefVIEx _ _ _ _ = 'False

type family IsDefVI (env :: EvalEnv) (phrase :: Phrase) :: Bool where
  IsDefVI env ('InfixAppl 'LogicalAnd p1 p2) = IsDefVI env p1 && IsDefVI env p2
  IsDefVI env p = IsDefVIEx (IsSubset (FTV p) (Vars env)) (IsDisjoint (FTV p) (Vars env)) env p

type DefVI env p = IsDefVI env p ~ 'True

type family ReplacePredicate (env :: EvalEnv) (phrase :: Phrase) :: Phrase where
  ReplacePredicate env ('InfixAppl 'LogicalAnd p1 p2) = ReplacePredicate env p1 :& ReplacePredicate env p2
  ReplacePredicate env p = If (IsSubset (FTV p) (Vars env)) (B 'True) p

type family Simplify (phrase :: Phrase) :: Phrase where
  Simplify ('InfixAppl 'LogicalAnd ('Constant ('Bool 'True)) p2) = p2
  Simplify ('InfixAppl 'LogicalAnd p1 ('Constant ('Bool 'True))) = p1
  Simplify p = p

type family Rem (phrase :: Phrase) (vs :: [Symbol]) :: Phrase where
  Rem ('InfixAppl 'LogicalAnd p1 p2) vs = 'InfixAppl 'LogicalAnd (Rem p1 vs) (Rem p2 vs)
  Rem p vs = If (IsDisjoint (FTV p) vs) p ('Constant ('Bool 'True))
