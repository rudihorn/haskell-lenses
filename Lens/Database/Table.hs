{-
  A module for manipulating database table definitions.
-}

{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications, OverloadedStrings #-}


module Lens.Database.Table where

import qualified Data.Set as Set
import qualified Data.Maybe as Maybe

import Data.Text.Format (Only(..))
import Data.Type.Set (Proxy(..))
import qualified Data.Text.Format as F (build)
import Data.Text.Lazy.Builder(Builder)
import Data.Text.Buildable (Buildable(..))

import Common
import Lens.Helpers.Format (build_sep_comma)
import Lens.Types (Type(..))
import Lens (Lens(..))
import Lens.Record.Base (RecoverEnv(..))
import Lens.Database.Base (LensQuery(..), LensDatabase(..))
import Tables (recover_tables)

data Column = Column
  { colName :: String
  , colTyp :: Type
  } deriving(Show)

data Table = Table
  { tblName :: String
  , tblColumns :: [Column]
  , tblKey :: Maybe [String]
  } deriving(Show)

db_type :: Type -> String
db_type Int = "INT"
db_type String = "TEXT"
db_type Bool = "BOOL"

build_col :: LensDatabase db => db -> Column -> IO Builder
build_col db col =
  do name <- escapeId db $ colName col
     return $ F.build "{} {}" (name, db_type $ colTyp col)

build_create_tbl_ifne  :: LensDatabase db => db -> Table -> IO Builder
build_create_tbl_ifne db tbl =
  do name <- escapeId db $ tblName tbl
     cols <- mapM (build_col db) $ tblColumns tbl
     keyOpt <- mapM pk $ Maybe.maybeToList $ tblKey tbl
     let opts = concat [cols, keyOpt]
     return $ F.build "CREATE TABLE IF NOT EXISTS {} ({})"
       (name, build_sep_comma cols) where
  pk cols =
     do cols <- mapM (escapeId db) cols
        return $ F.build "PRIMARY KEY ({})" (Only $ build_sep_comma cols)

{-| Create the database table if it does not exist. -}
create_ifne :: (LensQuery db, LensDatabase db) => db -> Lens ts rt p fds -> IO ()
create_ifne db (Prim :: Lens ts rt p fds) =
  do bld <- build_create_tbl_ifne db $ Table name cols key
     execute db bld where
  fds = recover @fds Proxy
  key = do (left, right) <- Maybe.listToMaybe fds
           let cols = Set.union (Set.fromList left) (Set.fromList right)
           let coversAll = Set.isSubsetOf (Set.fromList colNames) cols
           if coversAll then Just left else Nothing
  name = head $ recover_tables @ts Proxy
  cols = map (\(n,t) -> Column n t) $ recover_env @rt Proxy
  colNames = map colName cols

create_ifne db (Debug l) = create_ifne db l
create_ifne db (Join l1 l2) =
  do create_ifne db l1
     create_ifne db l2
create_ifne db (Select _ l) = create_ifne db l
create_ifne db (Drop _ _ l) = create_ifne db l
