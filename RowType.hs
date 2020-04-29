{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications #-}

module RowType where

import Data.List
import Data.Type.Bool
import Data.Type.Set (Proxy(..), (:++))
import GHC.TypeLits

import qualified Database.PostgreSQL.Simple.FromField as Fld

import Common
import Label
import Database.PostgreSQL.Simple.FromRow
import Database.PostgreSQL.Simple.Types(Only(..))

import qualified Types
import qualified Value
import qualified Types as T

type Env = [(Symbol, Types.Type)]

class RecoverEnv e where
  recover_env :: Proxy e -> [(String, Types.Type)]

instance RecoverEnv '[] where
  recover_env Proxy = []

instance (KnownSymbol k, Recoverable v Types.Type, RecoverEnv xs) => RecoverEnv ('(k,v) ': xs) where
  recover_env Proxy = (symbolVal (Proxy :: Proxy k), Types.recover_type (Proxy :: Proxy v)) : recover_env (Proxy :: Proxy xs)

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

type family LookupType (env :: Env) (s :: Symbol) :: Types.Type where
  LookupType '[] _ = 'Types.Int
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

data Row (e :: Env) where
  Empty :: Row '[]
  Cons :: Value.Value typ -> Row env -> Row ('( key, typ) ': env)

-- Make

data ValueList (t :: [Types.Type]) where
  EmptyV :: ValueList '[]
  ConsV :: Value.Value typ -> ValueList env -> ValueList (typ ': env)

-- Row Show

class Fields (e :: Env) where
  fields :: Row e -> [String]

instance Fields '[] where
  fields RowType.Empty = []

instance (KnownSymbol k, Show (Value.Value t), Fields xs) => Fields ( '(k, t) ': xs) where
  fields (Cons v r) = (symbolVal (Proxy :: Proxy k) ++ " = " ++ show v) : fields r

instance Fields e => Show (Row e) where
  show r = "{ " ++ flds ++ " }" where
    flds = concat $ intersperse ", " $ fields r



-- Row Fetching

class FetchRow t (i :: InEnvEvid) r where
  intfetch :: r -> Value.Value t

instance FetchRow t 'Take (Row ('(s, t) ': env)) where
  intfetch (Cons v _) = v

instance (FetchRow t evid (Row env)) => FetchRow t ('Skip evid) (Row ('(so, to) ': env))  where
  intfetch (Cons _ row) = intfetch @t @evid row

type Fetchable s env t evid = (
  t ~ LookupType env s,
  evid ~ Find env s,
  FetchRow t evid (Row env))

fetchv :: forall s env t evid. Fetchable s env t evid => (Row env) -> Value.Value t
fetchv row = intfetch @(LookupType env s) @(Find env s) row

fetch :: forall s env t evid. Fetchable s env t evid =>
  (Row env) -> Types.HaskellType t
fetch row = Value.valof (intfetch @t @evid row)



-- Row Updating
type family UpdateType (s :: Symbol) (t :: Types.Type) (env :: Env) :: Env where
  UpdateType _ _ '[] = '[]
  UpdateType s t ('(s, _) ': env) = '(s, t) ': env
  UpdateType s t ('(k,v) ': env) = '(k, v) ': (UpdateType s t env)

type family SetType (s :: Symbol) (t :: Types.Type) (env :: Env) (i :: Maybe InEnvEvid) :: Env where
  SetType s t env 'Nothing = '(s, t) ': env
  SetType s t ('(k, v) ': env) ('Just 'Take) = '(s, t) ': env
  SetType s t ('(k, v) ': env) ('Just ('Skip ev)) = '(k, v) ': (SetType s t env ('Just ev))

class UpdateRow s (t :: Types.Type) (r :: Env) (i :: Maybe InEnvEvid) where
  intupdate :: Value.Value t -> Row r -> Row (SetType s t r i)

instance UpdateRow s t ('(s, t1) ': env) ('Just 'Take) where
  intupdate v (Cons _ env) = Cons v env

type Same s t k v env = UpdateType s t ('(k, v) : env) ~ ('(k, v) : UpdateType s t env)

instance (UpdateRow s t env ('Just ev)) => UpdateRow s t ('(k, v) ': env) ('Just ('Skip ev)) where
  intupdate v (Cons w row :: Row ('(k, v) ': env)) = Cons w (intupdate @s @t @env @('Just ev) v row) :: Row ('(k, v) ': SetType s t (env) ('Just ev))

instance UpdateRow s t env 'Nothing where
  intupdate (v :: Value.Value t) row = Cons v row :: Row ('(s, t) ': env)

update :: forall s t env. (UpdateRow s (Types.LensType t) env (FindMaybe env s), Value.MakeValue t) => t -> Row env -> Row (SetType s (Types.LensType t) env (FindMaybe env s))
update v row = intupdate @s @(Types.LensType t) @env @(FindMaybe env s) (Value.make v) row

update_str :: forall s env. (UpdateRow s 'Types.String env (FindMaybe env s)) => String -> Row env -> Row (SetType s 'Types.String env (FindMaybe env s))
update_str v row = update @s v row

update_int :: forall s env. (UpdateRow s 'Types.Int env (FindMaybe env s)) => Int -> Row env -> Row (SetType s 'Types.Int env (FindMaybe env s))
update_int v row = update @s v row

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
  ProjectEnv (x ': xs) e = '(x, LookupType e x) ': ProjectEnv xs e

class Project (s :: [Symbol]) (e :: Env) where
  project :: Row e -> Row (ProjectEnv s e)

instance Project '[] env where
  project _ = RowType.Empty

instance (Project xs env, Fetchable x env t evid) => Project (x ': xs) (env) where
  project r = Cons (fetchv @x r) (project @xs @env r)

type Normalisable (e :: Env) = Project (SymAsSet (VarsEnv e)) e

type NormaliseEnv (e :: Env) = ProjectEnv (SymAsSet (VarsEnv e)) e

normalise :: Normalisable e => Row e -> Row (NormaliseEnv e)
normalise (r :: Row e) = project @(SymAsSet (VarsEnv e)) r


-- Join

type family JoinColumns (e1 :: Env) (e2 :: Env) :: [Symbol] where
  JoinColumns e1 e2 = SetIntersection (VarsEnv e1) (VarsEnv e2)

type family JoinEnv (e1 :: Env) (e2 :: Env) :: Env where
  JoinEnv e1 e2 = ProjectEnv (SetIntersection (VarsEnv e1) (VarsEnv e2)) e1

type family IsOverlappingJoinEx (e1 :: Env) (e2 :: Env) (join :: Env) :: Bool where
  IsOverlappingJoinEx e1 e2 join = Equal (ProjectEnv (VarsEnv join) e2) join

type family IsOverlappingJoin (e1 :: Env) (e2 :: Env) :: Bool where
  IsOverlappingJoin e1 e2 = IsOverlappingJoinEx e1 e2 (JoinEnv e1 e2)

type OverlappingJoin e1 e2 = OkOrError (IsOverlappingJoin e1 e2) ('Text "The types for the join column don't match.")

type family JoinRowTypes (e1 :: Env) (e2 :: Env) :: Env where
  JoinRowTypes e1 e2 = (RemoveEnv (VarsEnv (JoinEnv e1 e2)) e1) :++ e2

append :: Row rt -> Row rt' -> Row (rt :++ rt')
append Empty rt = rt
append (Cons v rt) rt' = Cons v (append rt  rt')

-- Examples


row1 :: Row '[ '( "A", 'Types.Int), '("B", 'Types.String)]
row1 = Cons (Value.Int 5) (Cons (Value.String "h") RowType.Empty)

row2 :: Row '[ '("B", 'Types.String)]
row2 = Cons (Value.String "h") RowType.Empty

row3 :: Row '[ '( "A", 'Types.Int), '("C", 'Types.Bool), '("B", 'Types.String)]
row3 = Cons (Value.Int 5) (Cons (Value.Bool True) (Cons (Value.String "h") RowType.Empty))


-- FetchRow

instance FromRow (Row '[]) where
  fromRow = return RowType.Empty

instance (Fld.FromField t0, FromRow (Row xs), Value.MakeValue t0, t0 ~ Types.HaskellType t, Types.LensType t0 ~ t) => FromRow (Row ('(k, t) ': xs)) where
  fromRow = Cons <$> (Value.make @t0 <$> field) <*> fromRow @(Row xs)


-- Equal

instance Eq (Row e) where
  RowType.Empty == RowType.Empty = True
  Cons v vs == Cons v' vs' = v == v' && vs == vs'


-- Compare

instance Ord (Row e) where
  compare Empty RowType.Empty = EQ
  compare (Cons v vs) (Cons v' vs') = compare v v' <> compare vs vs'


-- Helper Syntax

type family TupleType (e :: Env) :: * where
  TupleType '[ '(k, t)] = Only (T.HaskellType t)
  TupleType '[ '(k1, t1), '(k2, t2)] = (T.HaskellType t1, T.HaskellType t2)
  TupleType '[ '(k1, t1), '(k2, t2), '(k3, t3)] =
    (T.HaskellType t1, T.HaskellType t2, T.HaskellType t3)
  TupleType '[ '(k1, t1), '(k2, t2), '(k3, t3), '(k4, t4)] =
    (T.HaskellType t1, T.HaskellType t2, T.HaskellType t3, T.HaskellType t4)
  TupleType '[ '(k1, t1), '(k2, t2), '(k3, t3), '(k4, t4), '(k5, t5)] =
    (T.HaskellType t1, T.HaskellType t2, T.HaskellType t3, T.HaskellType t4, T.HaskellType t5)

class ToRow rt vals where
  toRow :: vals -> Row rt

type VVal v t = (Value.MakeValueEx v t)

mkval :: VVal v t => v -> Value.Value t
mkval v = Value.makeEx v

instance VVal v t => ToRow '[ '(k, t)] (Only v) where
  toRow (Only v) = Cons (mkval v) Empty

instance (VVal v1 t1, VVal v2 t2) => ToRow '[ '(k1, t1), '(k2, t2)] (v1, v2) where
  toRow (v1, v2) = Cons (mkval v1) $ Cons (mkval v2) Empty

instance (VVal v1 t1, VVal v2 t2, VVal v3 t3) => ToRow '[ '(k1, t1), '(k2, t2), '(k3, t3)] (v1, v2, v3) where
  toRow (v1, v2, v3) = Cons (mkval v1) $ Cons (mkval v2) $ Cons (mkval v3) Empty

instance (VVal v1 t1, VVal v2 t2, VVal v3 t3, VVal v4 t4) => ToRow '[ '(k1, t1), '(k2, t2), '(k3, t3), '(k4, t4)] (v1, v2, v3, v4) where
  toRow (v1, v2, v3, v4) = Cons (mkval v1) $ Cons (mkval v2) $ Cons (mkval v3) $ Cons (mkval v4) Empty

instance (VVal v1 t1, VVal v2 t2, VVal v3 t3, VVal v4 t4, VVal v5 t5) => ToRow '[ '(k1, t1), '(k2, t2), '(k3, t3), '(k4, t4), '(k5, t5)] (v1, v2, v3, v4, v5) where
  toRow (v1, v2, v3, v4, v5) = Cons (mkval v1) $ Cons (mkval v2) $ Cons (mkval v3) $ Cons (mkval v4) $ Cons (mkval v5) Empty


--fetch :: forall (s :: Symbol) (typ :: Types.Type) (env :: Env).
--fetch :: forall (s :: Symbol) (typ :: Types.Type) (env :: Env).
--  InEnv env s typ => Row env -> (Types.HaskellType typ)
-- fetch row = 5
