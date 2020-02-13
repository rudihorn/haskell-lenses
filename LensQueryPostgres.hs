{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module LensQueryPostgres where

import Database.PostgreSQL.Simple(query_, connect, defaultConnectInfo, connectDatabase, connectUser, connectPassword)
import Database.PostgreSQL.Simple.Types(Query(..), fromQuery)
import Database.PostgreSQL.Simple.Internal(escapeIdentifier, escapeStringConn)
import Database.PostgreSQL.Simple.FromRow
import Lens
import LensQuery
import RowType
import Data.Either
import Data.Text.Format
import Data.Text.Lazy.Builder(toLazyText)
import Data.ByteString.UTF8 as BLU
import Data.ByteString.Lazy as BL
import Data.Text.Lazy.Encoding as TLE


query :: (FromRow (Row r), Fields r, LensQueryable t r p) => Lens t r p fds -> IO ()
query (l :: Lens t r p fds) = do
  conn <- connect defaultConnectInfo {
    connectDatabase = "links",
    connectUser = "links",
    connectPassword = "links"
  }
  let lft f arg = build "{}" <$> Only <$> BLU.toString <$> fromRight "error" <$> f conn (BLU.fromString arg)
  let db = (lft escapeIdentifier, lft escapeStringConn)
  q <- build_query db l
  mapM_ Prelude.print =<< (query_ conn (Query { fromQuery = BL.toStrict $ TLE.encodeUtf8 $ toLazyText q}) :: IO [Row r])
