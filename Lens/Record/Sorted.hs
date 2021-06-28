{-# LANGUAGE ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes,
             FlexibleContexts, ConstraintKinds, UndecidableInstances,
             MultiParamTypeClasses, RankNTypes #-}

module Lens.Record.Sorted where

import Data.Map.Strict ((!?))
import Data.Set (Set, toList)
import Data.Type.Set ((:++))

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

import Lens.Predicate.Compile (LookupMap, compile)
import Delta (Delta)
import Lens.Predicate.Dynamic (DPhrase)
import Label (IsSubset, AdjustOrder)
import FunDep (FunDep, Left, Right)
import Lens.Record.Base (append, Env, Row, Project, ProjectEnv, RemoveInterEnv, JoinEnv, VarsEnv, ToRow, toRow)

import qualified Lens.Predicate.Dynamic as DP
import qualified Label as L
import qualified Lens.Record.Base as R

type RecordsSet rt = Set (Row rt)
type RecordsDelta rt = Delta (Row rt)

type RemainingColumns rt rt' = L.Subtract (R.VarsEnv rt') (R.InterCols rt rt')

type ProjectJoin rt rt' rt'' = ProjectEnv (R.InterCols rt rt') rt''

type Joinable rt rt' rt'' =
  (ProjectEnv (R.VarsEnv rt'') (ProjectEnv (VarsEnv (RemoveInterEnv rt rt')) rt :++ rt') ~ rt'',
   ProjectJoin rt rt' rt ~ ProjectJoin rt rt' rt',
   Project (R.InterCols rt rt') rt,
   Project (R.InterCols rt rt') rt',
   Project (VarsEnv (RemoveInterEnv rt rt')) rt,
   Project (R.VarsEnv rt'') (ProjectEnv (VarsEnv (RemoveInterEnv rt rt')) rt :++ rt'))

join :: forall rt'' rt rt'. Joinable rt rt' rt'' => RecordsSet rt -> RecordsSet rt' -> RecordsSet rt''
join rs ss = Set.fromList $ concat $ map f_entry $ Set.toList ss where
  join_map = Map.fromListWith (++) $ map join_entry $ Set.toList rs
  join_entry r =
    (R.project @(R.InterCols rt rt') r,
     [R.project @(VarsEnv (RemoveInterEnv rt rt')) r])
  f_entry s =
    case join_map !? R.project @(R.InterCols rt rt') s of
    Nothing -> []
    Just r -> map (\r -> R.project @(R.VarsEnv rt'') (append r s)) r

project :: forall s rt. (Project s rt) => RecordsSet rt -> RecordsSet (ProjectEnv s rt)
project rs = Set.map (R.project @s) rs

map_rs :: (Row rt -> Row rt') -> RecordsSet rt -> RecordsSet rt'
map_rs = Set.map

filter :: forall rt. LookupMap rt => DPhrase -> RecordsSet rt -> RecordsSet rt
filter p recs = Set.filter f recs where
  f r = fpred r == DP.Bool True
  fpred = compile @rt p


-- relatinoal merge

type RevisableFdEx left right adj_right rt rt' =
  (IsSubset adj_right right ~ 'True,
   Project left rt, Project left rt',
   R.ProjectEnv left rt ~ R.ProjectEnv left rt',
   R.Revisable rt (R.ProjectEnv adj_right rt'),
   Project adj_right rt')

type RevisableFd fd rt rt' = RevisableFdEx (Left fd) (Right fd) (AdjustOrder (Right fd) (VarsEnv rt)) rt rt'

revise_fd :: forall (fd :: FunDep) rt rt'.
  (RevisableFd fd rt rt') =>
  RecordsSet rt -> RecordsSet rt' -> RecordsSet rt
revise_fd m n =  Set.map update m where
  map = Map.fromList $ Set.toList $ Set.map f_row n
  f_row r = (R.project @(Left fd) r, R.project @(AdjustOrder (Right fd) (VarsEnv rt)) r)
  update r =
    case Map.lookup (R.project @(Left fd) r) map of
      Nothing -> r
      Just s ->  R.revise r s

class Revisable (fds :: [FunDep]) (rt :: Env) (rt' :: Env) where
  revise :: RecordsSet rt -> RecordsSet rt' -> RecordsSet rt

instance Revisable '[] rt rt' where
  revise r s = r

instance (RevisableFd fd rt rt', Revisable fds rt rt') => Revisable (fd ': fds) rt rt' where
  revise r s = revise_fd @fd (revise  @fds r s) s

merge :: forall fds rt. Revisable fds rt rt => RecordsSet rt -> RecordsSet rt -> RecordsSet rt
merge r s = revise @fds r s `Set.union` s

recs :: forall rt vals. (vals ~ R.TupleType rt, ToRow rt vals) => [vals] -> RecordsSet rt
recs vals = Set.fromList $ map (toRow @rt) vals

rows :: forall rt vals. (vals ~ R.TupleType rt, ToRow rt vals) => [vals] -> RecordsSet rt
rows = recs
