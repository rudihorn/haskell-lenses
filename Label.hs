{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving #-}

module Label where

import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Set
import Data.List
import Data.Kind

data Lab :: Symbol -> * where
  Lab :: Lab l

class LabKnown f where
  labVal :: f -> String

instance KnownSymbol s => LabKnown (Lab s) where
  labVal _ = symbolVal (Proxy :: Proxy s)

data LabList :: [Symbol] -> * where
  LabList :: LabList l

ex = LabList :: LabList '["B", "C"]

class LabListKnown f where
  labListVal :: f -> [String]

instance LabListKnown (LabList '[]) where
  labListVal _ = []

instance (KnownSymbol x, LabListKnown (LabList xs)) => LabListKnown (LabList (x ': xs)) where
  labListVal _ = labVal (Lab :: Lab x) : (labListVal (LabList :: LabList xs))

type family IsElement (s :: Symbol) (r :: [Symbol]) :: Bool where
  IsElement _ '[] = 'False
  IsElement x (x ': xs) = 'True
  IsElement x (y ': ys) = IsElement x ys

type family IsSubset (l :: [Symbol]) (r :: [Symbol]) :: Bool where
  IsSubset '[] _ = 'True
  IsSubset (x ': xs) ys = IsElement x ys && IsSubset xs ys

type family IsDisjoint (l :: [Symbol]) (r :: [Symbol]) :: Bool where
  IsDisjoint '[] _ = 'True
  IsDisjoint (x ': xs) ys = Not (IsElement x ys) && IsDisjoint xs ys

type family DisjointFromAll (s :: [Symbol]) (xs :: [[Symbol]]) :: Bool where
  DisjointFromAll xs '[]  = 'True
  DisjointFromAll xs (y ': ys) = IsDisjoint xs y && DisjointFromAll xs ys

type family AllDisjoint (s :: [[Symbol]]) :: Bool where
  AllDisjoint '[] = 'True
  AllDisjoint (x ': xs) = DisjointFromAll x xs && AllDisjoint xs

type family IsEqual (l :: [Symbol]) (r :: [Symbol]) :: Bool where
  IsEqual l l = 'True
  IsEqual _ _ = 'False

type family LabUnion (l :: [Symbol]) (r :: [Symbol]) :: [Symbol] where
  LabUnion '[] ys = ys
  LabUnion (x ': xs) ys = If (IsElement x ys) (LabUnion xs ys) (x ': (LabUnion xs ys))

type family SetSubtract (l :: [Symbol]) (r :: [Symbol]) :: [Symbol] where
  SetSubtract '[] _ = '[]
  SetSubtract (x ': xs) ys = If (IsElement x ys) (SetSubtract xs ys) (x ': SetSubtract xs ys)

type family Len (l :: [k]) :: Nat where
  Len '[] = 0
  Len (_ ': xs) = 1 + (Len xs)

data SymFlag = SymFMin | SymFMax

type family SymSort (xs :: [k]) :: [k] where
  SymSort '[] = '[]
  SymSort (x ': xs) = ((SymSort (SymFilter 'SymFMin x xs)) :++ '[x]) :++ (SymSort (SymFilter 'SymFMax x xs))

type family SymFilterLT (x :: k) (xs :: [k]) (o :: Ordering) :: [k] where
  SymFilterLT x xs 'LT = x ': xs
  SymFilterLT x xs _ = xs

type family SymFilter (f :: SymFlag) (p :: k) (xs :: [k]) :: [k] where
  SymFilter f p '[] = '[]
  SymFilter 'SymFMin p (x ': xs) = SymFilterLT x (SymFilter 'SymFMin p xs) (CmpSymbol x p)
  SymFilter 'SymFMax p (x ': xs) = SymFilterLT x (SymFilter 'SymFMax p xs) (CmpSymbol p x)

type family SymNub (t :: [k]) :: [k] where
  SymNub '[] = '[]
  SymNub '[e] = '[e]
  SymNub (e ': e ': s) = SymNub (e ': s)
  SymNub (e ': f ': s) = e ': SymNub (f ': s)

type family SymAsSet (t :: [k]) :: [k] where
  SymAsSet s = SymNub (SymSort s)

type family SymUnion (s :: [k]) (t :: [k]) :: [k] where
  SymUnion s t = SymAsSet (s :++ t)

type family SLCmpHelper (s :: [Symbol]) (t :: [Symbol]) (o :: Ordering) :: Ordering where
  SLCmpHelper xs ys 'EQ = SLCmp xs ys
  SLCmpHelper xs ys 'LT = 'LT
  SLCmpHelper xs ys 'GT = 'GT

type family SLCmp (s :: [Symbol]) (t :: [Symbol]) :: Ordering where
  SLCmp '[] '[] = 'EQ
  SLCmp '[] _ = 'LT
  SLCmp _ '[] = 'GT
  SLCmp (x ': xs) (y ': ys) = SLCmpHelper xs ys (CmpSymbol x y)

type family SLFilterLT (x :: k) (xs :: [k]) (o :: Ordering) :: [k] where
  SLFilterLT x xs 'LT = x ': xs
  SLFilterLT x xs _ = xs

type family SLFilter (f :: SymFlag) (p :: k) (xs :: [k]) :: [k] where
  SLFilter f p '[] = '[]
  SLFilter 'SymFMin p (x ': xs) = SLFilterLT x (SLFilter 'SymFMin p xs) (SLCmp x p)
  SLFilter 'SymFMax p (x ': xs) = SLFilterLT x (SLFilter 'SymFMax p xs) (SLCmp p p)

type family SLSort (xs :: [k]) :: [k] where
  SLSort '[] = '[]
  SLSort (x ': xs) = ((SLSort (SLFilter 'SymFMin x xs)) :++ '[x]) :++ (SLSort (SLFilter 'SymFMax x xs))

type family SLAsSet (t :: [k]) :: [k] where
  SLAsSet s = SymNub (SLSort s)

ppList :: String -> [String] -> String
ppList = intercalate

printLabList :: LabListKnown (LabList xs) => LabList xs -> String
printLabList l = ppList " " $ labListVal l

instance LabListKnown (LabList s) => Show (LabList s) where
  show _ = printLabList (LabList :: LabList s)

