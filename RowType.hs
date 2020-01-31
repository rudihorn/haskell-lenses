{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications #-}

module RowType where

import Common
import Data.List
import Data.Type.Bool
import Data.Type.Set
import GHC.TypeLits
import Label
import qualified Types
import qualified Value
import Database.PostgreSQL.Simple.FromRow
import qualified Database.PostgreSQL.Simple.FromField as Fld

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

type family Find (env :: Env) (s :: Symbol) :: InEnvEvid where
  Find ('(key, val) ': env) key = 'Take
  Find ('(other, val) ': env) key = 'Skip (Find env key)


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

type Fetchable s env = FetchRow (LookupType env s) (Find env s) (Row env)

fetchv :: forall s env. Fetchable s env => (Row env) -> Value.Value (LookupType env s)
fetchv row = intfetch @(LookupType env s) @(Find env s) row

fetch :: forall s env. Fetchable s env => (Row env) -> Types.HaskellType (LookupType env s)
fetch row = Value.valof (intfetch @(LookupType env s) @(Find env s) row)



-- Row Updating
type family UpdateType (s :: Symbol) (t :: Types.Type) (env :: Env) :: Env where
  UpdateType _ _ '[] = '[]
  UpdateType s t ('(s, _) ': env) = '(s, t) ': env
  UpdateType s t ('(k,v) ': env) = '(k, v) ': (UpdateType s t env)

class UpdateRow s (t :: Types.Type) (r :: Env) (i :: InEnvEvid) where
  intupdate :: Value.Value t -> Row r -> Row (UpdateType s t r)

instance UpdateRow s t ('(s, t1) ': env) 'Take where
  intupdate v (Cons _ env) = Cons v env

type Same s t k v env = UpdateType s t ('(k, v) : env) ~ ('(k, v) : UpdateType s t env)

instance (UpdateRow s t env ev, Same s t k v env) => UpdateRow s t ('(k, v) ': env) ('Skip ev) where
  intupdate v (Cons w row :: Row ('(k, v) ': env)) = Cons w (intupdate @s @t @env @ev v row) :: Row ('(k, v) ': UpdateType s t (env))

update :: forall s t env. (UpdateRow s (Types.LensType t) env (Find env s), Value.MakeValue t) => t -> Row env -> Row (UpdateType s (Types.LensType t) env)
update v row = intupdate @s @(Types.LensType t) @env @(Find env s) (Value.make v) row


-- Projection

type family ProjectEnv (s :: [Symbol]) (e :: Env) where
  ProjectEnv '[] _ = '[]
  ProjectEnv (x ': xs) e = '(x, LookupType e x) ': ProjectEnv xs e

class Project (s :: [Symbol]) (e :: Env) where
  project :: Row e -> Row (ProjectEnv s e)

instance Project '[] env where
  project _ = RowType.Empty

instance (Project xs env, Fetchable x env) => Project (x ': xs) (env) where
  project r = Cons (fetchv @x r) (project @xs @env r)

type Normalisable (e :: Env) = Project (SymAsSet (VarsEnv e)) e

type NormaliseEnv (e :: Env) = ProjectEnv (SymAsSet (VarsEnv e)) e

normalise :: Normalisable e => Row e -> Row (NormaliseEnv e)
normalise (r :: Row e) = project @(SymAsSet (VarsEnv e)) r


-- Join

type family JoinColumns (e1 :: Env) (e2 :: Env) :: Env where
  JoinColumns e1 e2 = ProjectEnv (SetIntersection (VarsEnv e1) (VarsEnv e2)) e1

type family IsOverlappingJoinEx (e1 :: Env) (e2 :: Env) (join :: Env) :: Bool where
  IsOverlappingJoinEx e1 e2 join = Equal (ProjectEnv (VarsEnv join) e2) join

type family IsOverlappingJoin (e1 :: Env) (e2 :: Env) :: Bool where
  IsOverlappingJoin e1 e2 = IsOverlappingJoinEx e1 e2 (JoinColumns e1 e2)

type OverlappingJoin e1 e2 = OkOrError (IsOverlappingJoin e1 e2) ('Text "The types for the join column don't match.")

type family JoinRowTypes (e1 :: Env) (e2 :: Env) :: Env where
  JoinRowTypes e1 e2 = (RemoveEnv (VarsEnv (JoinColumns e1 e2)) e1) :++ e2

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

--fetch :: forall (s :: Symbol) (typ :: Types.Type) (env :: Env).
--fetch :: forall (s :: Symbol) (typ :: Types.Type) (env :: Env).
--  InEnv env s typ => Row env -> (Types.HaskellType typ)
-- fetch row = 5
