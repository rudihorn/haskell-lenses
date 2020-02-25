{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses,
             DataKinds, PolyKinds, KindSignatures, UndecidableInstances,
             TypeApplications #-}

module LensQueryPostgres (PostgresDatabase, query) where

import Data.Type.Set (Proxy(..))

import Database.PostgreSQL.Simple(
  Connection, query_, connect, defaultConnectInfo,
  connectDatabase, connectUser, connectPassword)
import Database.PostgreSQL.Simple.Types(Query(..), fromQuery)
import Database.PostgreSQL.Simple.Internal(
  escapeIdentifier, escapeStringConn)
import Database.PostgreSQL.Simple.FromRow
import Lens
import LensQuery
import LensDatabase
import DynamicPredicate as DP
import RowType
import Data.Either
import Data.Text.Format
import Data.Text.Lazy.Builder (Builder, toLazyText)
import Data.ByteString.UTF8 as BLU
import Data.ByteString.Lazy as BL
import Data.Text.Lazy.Encoding as TLE

type PostgresDatabase = Connection

lft :: PostgresDatabase ->
       (PostgresDatabase -> BLU.ByteString -> IO (Either a BLU.ByteString)) ->
       String -> IO Builder
lft conn f arg =
    build "{}" <$>
    Only <$>
    BLU.toString <$>
    fromRight "error" <$>
    f conn (BLU.fromString arg)

instance LensDatabase PostgresDatabase where
  escapeId c str = lft c escapeIdentifier str
  escapeStr c str = build "'{}'" <$> Only <$> lft c escapeStringConn str

instance LensQuery PostgresDatabase where
  query c l = query' c l (lensToFromRowHack l) where
    -- query' :: PostgresDatabase -> (Lens ts rt p fds) -> (FromRowHack rt) -> IO [Row rt]
    query' c l Hack =
      do q <- build_query c l
         let qstr = BL.toStrict $ TLE.encodeUtf8 $ toLazyText q
         query_ c (Query { fromQuery = qstr })
  query_ex (Proxy :: Proxy rt) c tables cols_map p = do
    let cols = Prelude.map fst $ recover_env @rt Proxy
    q <- build_query_ex c tables cols cols_map p
    let qstr = BL.toStrict $ TLE.encodeUtf8 $ toLazyText q
    query_ c (Query { fromQuery = qstr })
