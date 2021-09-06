{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications, RankNTypes, QuantifiedConstraints #-}

module Lens.Record.Base where

import Data.List
import Data.Type.Bool
import Data.Type.Set (Proxy(..), (:++))
import GHC.TypeLits

import qualified Database.PostgreSQL.Simple.FromField as Fld

import Common
import Label
import Database.PostgreSQL.Simple.FromRow
import Database.PostgreSQL.Simple.Types(Only(..))

import qualified Lens.Types as T
import qualified Value

type Env = [(Symbol, *)]

class RecoverEnv e where
  recover_env :: Proxy e -> [(String, T.Type)]

instance RecoverEnv '[] where
  recover_env Proxy = []

instance (KnownSymbol k, Recoverable v T.Type, RecoverEnv xs) => RecoverEnv ('(k,v) ': xs) where
  recover_env Proxy = (symbolVal (Proxy :: Proxy k), T.recover_type (Proxy :: Proxy v)) : recover_env (Proxy :: Proxy xs)

type family VarsEnv (env :: Env) :: [Symbol] where
  VarsEnv '[] = '[]
  VarsEnv ( '(k, v) ': env) = k ': (VarsEnv env)

type family RemoveEnv (vars :: [Symbol]) (env :: Env) where
  RemoveEnv vs '[] = '[]
  RemoveEnv vs ( '(k, v) ': xs) = If (IsElement k vs) (RemoveEnv vs xs) ( '(k, v) ': RemoveEnv vs xs)

type family Intersection (e1 :: Env) (e2 :: Env)

data InEnvEvid where
  Take :: InEnvEvid
  Skip :: InEnvEvid -> InEnvEvid

type family EvidType (env :: Env) (s :: InEnvEvid) :: * where
  EvidType ('(_, val) ': _) 'Take = val
  EvidType (_ ': xs) ('Skip evid) = EvidType xs evid

type family LookupType (env :: Env) (s :: Symbol) :: * where
  LookupType '[] _ = Int
  LookupType ('(key, val) ': xs) key = val
  LookupType (_ ': xs) key = LookupType xs key

type family SkipMaybe (s :: Maybe InEnvEvid) :: Maybe InEnvEvid where
  SkipMaybe 'Nothing = 'Nothing
  SkipMaybe ('Just x) = 'Just ('Skip x)

type family FindMaybe (env :: Env) (s :: Symbol) :: Maybe InEnvEvid where
  FindMaybe '[] _ = 'Nothing
  FindMaybe ('(key, val) ': env) key = 'Just 'Take
  FindMaybe ('(other, val) ': env) key = SkipMaybe (FindMaybe env key)

type family Find (env :: Env) (s :: Symbol) :: InEnvEvid where
  Find env s = UnpackMaybe (FindMaybe env s)

type family FindAlt (env :: Env) (s :: Symbol) :: InEnvEvid where
  FindAlt ('(key, _) ': env) key = 'Take
  FindAlt ('(_, val) ': env) key = 'Skip (FindAlt env key)

data Row (e :: Env) where
  Empty :: Row '[]
  Cons :: (Ord t, Eq t) => t -> Row env -> Row ('( key, t) ': env)

-- Make

data ValueList (t :: [T.Type]) where
  EmptyV :: ValueList '[]
  ConsV :: Value.Value typ -> ValueList env -> ValueList (typ ': env)

-- Row Show

class Fields (e :: Env) where
  fields :: Row e -> [String]

instance Fields '[] where
  fields Empty = []

instance (KnownSymbol k, Show t, Fields xs) => Fields ( '(k, t) ': xs) where
  fields (Cons v r) = (symbolVal (Proxy :: Proxy k) ++ " = " ++ show v) : fields r

instance Fields e => Show (Row e) where
  show r = "{ " ++ flds ++ " }" where
    flds = concat $ intersperse ", " $ fields r



-- Row Fetching

class FetchRow t (i :: InEnvEvid) r where
  intfetch :: r -> t

instance FetchRow t 'Take (Row ('(s, t) ': env)) where
  intfetch (Cons v _) = v

instance (FetchRow t evid (Row env)) => FetchRow t ('Skip evid) (Row ('(so, to) ': env))  where
  intfetch (Cons _ row) = intfetch @t @evid row

type Fetchable s env t evid = (
  t ~ EvidType env evid,
  Ord t,
  Eq t,
  evid ~ Find env s,
  FetchRow t evid (Row env))

type Test s env t = forall evid. Fetchable s env t evid

fetch :: forall s env t evid. Fetchable s env t evid => Row env -> t
fetch row = intfetch @t @evid row



type family UpdateType (s :: Symbol) (t :: *) (env :: Env) :: Env where
  UpdateType _ _ '[] = '[]
  UpdateType s t ('(s, _) ': env) = '(s, t) ': env
  UpdateType s t ('(k,v) ': env) = '(k, v) ': (UpdateType s t env)

type Same s t k v env = UpdateType s t ('(k, v) : env) ~ ('(k, v) : UpdateType s t env)


-- Row Updating

type family SetType (s :: Symbol) (t :: *) (env :: Env) (i :: Maybe InEnvEvid) :: Env where
  SetType s t env 'Nothing = '(s, t) ': env
  SetType s t ('(k, v) ': env) ('Just 'Take) = '(s, t) ': env
  SetType s t ('(k, v) ': env) ('Just ('Skip ev)) = '(k, v) ': (SetType s t env ('Just ev))

class UpdateRow s (t :: *) (r :: Env) (i :: Maybe InEnvEvid) where
  intupdate :: Ord t => t -> Row r -> Row (SetType s t r i)

instance UpdateRow s t ('(s, t1) ': env) ('Just 'Take) where
  intupdate v (Cons _ env) = Cons v env

instance (UpdateRow s t env ('Just ev)) => UpdateRow s t ('(k, v) ': env) ('Just ('Skip ev)) where
  intupdate v (Cons w row) = Cons w (intupdate @s @t @env @('Just ev) v row)

instance UpdateRow s t env 'Nothing where
  intupdate v row = Cons v row

type Updatable s t env tnew evid = (
  evid ~ FindMaybe env s,
  UpdateRow s t env evid,
  tnew ~ SetType s t env evid,
  Ord t)

update :: forall s t env tnew evid. (Updatable s t env tnew evid) => t -> Row env -> Row tnew
update v row = intupdate @s @t @env @(FindMaybe env s) v row



-- Revision

class IntRevisable (rt :: Env) (rt' :: Env) (i :: Maybe InEnvEvid) where
  intrevise :: Row rt -> Row rt' -> Row rt

type family RevisableEvid (rt :: Env) (rt' :: Env) where
  RevisableEvid rt '[] = 'Nothing
  RevisableEvid rt ('(k, v) ': rst) = FindMaybe rt k

instance IntRevisable rt '[] ('Nothing) where
  intrevise r _ = r

instance IntRevisable rs1 rs2 (RevisableEvid rs1 rs2) =>
  IntRevisable ('(k, t) ':  rs1) ('(k, t) ': rs2) ('Just 'Take) where
  intrevise (Cons _ row) (Cons v rst) = Cons v (intrevise @rs1 @rs2 @(RevisableEvid rs1 rs2) row rst)

instance IntRevisable rs1 rs2 ('Just evid) => IntRevisable ('(k, t) ': rs1) rs2 ('Just ('Skip evid)) where
  intrevise (Cons v row) rs = Cons v (intrevise @rs1 @rs2 @('Just evid) row rs)

type Revisable rs1 rs2 = IntRevisable rs1 rs2 (RevisableEvid rs1 rs2)

revise :: forall rs1 rs2. Revisable rs1 rs2 => Row rs1 -> Row rs2 -> Row rs1
revise r s = intrevise @rs1 @rs2 @(RevisableEvid rs1 rs2) r s

-- Projection

type family ProjectEnv (s :: [Symbol]) (e :: Env) where
  ProjectEnv '[] _ = '[]
  ProjectEnv (x ': xs) e = '(x, EvidType e (Find e x)) ': ProjectEnv xs e

class Project (s :: [Symbol]) (e :: Env) where
  project :: Row e -> Row (ProjectEnv s e)

instance Project '[] env where
  project _ = Empty

instance (Project xs env, Fetchable x env t evid) => Project (x ': xs) (env) where
  project r = Cons (fetch @x r) (project @xs @env r)

type Normalisable (e :: Env) = Project (SymAsSet (VarsEnv e)) e

type NormaliseEnv (e :: Env) = ProjectEnv (SymAsSet (VarsEnv e)) e

normalise :: Normalisable e => Row e -> Row (NormaliseEnv e)
normalise (r :: Row e) = project @(SymAsSet (VarsEnv e)) r


-- Join

type family InterCols (e1 :: Env) (e2 :: Env) :: [Symbol] where
  InterCols e1 e2 = SetIntersection (VarsEnv e1) (VarsEnv e2)

type family InterEnv (e1 :: Env) (e2 :: Env) :: Env where
  InterEnv e1 e2 = ProjectEnv (InterCols e1 e2) e1

type family InterRow (r1 :: *) (r2 :: *) :: * where
  InterRow (Row e1) (Row e2) = Row (InterEnv e1 e2)

type family IsOverlappingJoinEx (e1 :: Env) (e2 :: Env) (join :: Env) :: Bool where
  IsOverlappingJoinEx e1 e2 join = Equal (ProjectEnv (VarsEnv join) e2) join

type family IsOverlappingJoin (e1 :: Env) (e2 :: Env) :: Bool where
  IsOverlappingJoin e1 e2 = IsOverlappingJoinEx e1 e2 (InterEnv e1 e2)

type OverlappingJoin e1 e2 = OkOrError (IsOverlappingJoin e1 e2) ('Text "The types for the join column don't match.")

type family RemoveInterEnv (e1 :: Env) (e2 :: Env) :: Env where
  RemoveInterEnv e1 e2 = (RemoveEnv (VarsEnv (InterEnv e1 e2)) e1)

type family JoinEnv (e1 :: Env) (e2 :: Env) :: Env where
  JoinEnv e1 e2 = RemoveInterEnv e1 e2 :++ e2

append :: Row rt -> Row rt' -> Row (rt :++ rt')
append Empty rt = rt
append (Cons v rt) rt' = Cons v (append rt  rt')

-- Examples


row1 :: Row '[ '( "A", Int), '("B", String)]
row1 = Cons 5 $ Cons "h" Empty

row2 :: Row '[ '("B", String)]
row2 = Cons "h" Empty

row3 :: Row '[ '( "A", Int), '("C", Bool), '("B", String)]
row3 = Cons 5 $ Cons True $ Cons "h" Empty


-- FetchRow

instance FromRow (Row '[]) where
  fromRow = return Empty

instance (Ord t, Fld.FromField t, FromRow (Row xs)) => FromRow (Row ('(k, t) ': xs)) where
  fromRow = Cons <$> field <*> fromRow @(Row xs)


-- Equal
comp :: Row e -> Row e -> Ordering
comp Empty Empty = EQ
comp (Cons v vs) (Cons v' vs') = compare v v' <> comp vs vs'

eq :: Row e -> Row e -> Bool
eq Empty Empty = True
eq (Cons v vs) (Cons v' vs') = v == v' && eq vs vs'

-- Compare

instance Eq (Row e) where
  r1 == r2 = eq r1 r2

instance Ord (Row e) where
  compare r1 r2 = comp r1 r2


-- Helper Syntax

type family TupleType (e :: Env) :: * where
  TupleType '[ '(k, t)] = Only (t)
  TupleType '[ '(k1, t1), '(k2, t2)] = (t1, t2)
  TupleType '[ '(k1, t1), '(k2, t2), '(k3, t3)] = (t1, t2, t3)
  TupleType '[ '(k1, t1), '(k2, t2), '(k3, t3), '(k4, t4)] = (t1, t2, t3, t4)
  TupleType '[ '(k1, t1), '(k2, t2), '(k3, t3), '(k4, t4), '(k5, t5)] = (t1, t2, t3, t4, t5)

class ToRow rt vals where
  toRow :: vals -> Row rt

type Req t = (Ord t, Eq t)

instance (Req t) => ToRow '[ '(k, t)] (Only t) where
  toRow (Only v) = Cons v Empty

instance (Req t1, Req t2) => ToRow '[ '(k1, t1), '(k2, t2)] (t1, t2) where
  toRow (v1, v2) = Cons (v1) $ Cons (v2) Empty

instance (Req t1, Req t2, Req t3) => ToRow '[ '(k1, t1), '(k2, t2), '(k3, t3)] (t1, t2, t3) where
  toRow (v1, v2, v3) = Cons v1 $ Cons v2 $ Cons v3 Empty

instance (Req t1, Req t2, Req t3, Req t4) => ToRow '[ '(k1, t1), '(k2, t2), '(k3, t3), '(k4, t4)] (t1, t2, t3, t4) where
  toRow (v1, v2, v3, v4) = Cons v1 $ Cons v2 $ Cons v3 $ Cons v4 Empty

instance (Req t1, Req t2, Req t3, Req t4, Req t5) => ToRow '[ '(k1, t1), '(k2, t2), '(k3, t3), '(k4, t4), '(k5, t5)] (t1, t2, t3, t4, t5) where
  toRow (v1, v2, v3, v4, v5) = Cons v1 $ Cons v2 $ Cons v3 $ Cons v4 $ Cons v5 Empty

--fetch :: forall (s :: Symbol) (typ :: Types.Type) (env :: Env).
--fetch :: forall (s :: Symbol) (typ :: Types.Type) (env :: Env).
--  InEnv env s typ => Row env -> (Types.HaskellType typ)
-- fetch row = 5
