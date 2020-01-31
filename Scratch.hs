{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module Scratch where

import Control.Monad
import Control.Applicative
import Control.Monad.State.Lazy
import Database.PostgreSQL.Simple(query_, connect, defaultConnectInfo, connectDatabase, connectUser, connectPassword)
import Database.PostgreSQL.Simple.Types(Query(..), fromQuery)
import Database.PostgreSQL.Simple.Internal(escapeIdentifier, escapeStringConn)
import Database.PostgreSQL.Simple.FromRow
-- import Database.PostgreSQL.Simple.Types
import qualified Types as T
import RowType
import Lens
import LensQuery
import Data.Text.Format
import Data.Text.Lazy.Builder(toLazyText)
import qualified Data.String as BS
import Data.ByteString.UTF8 as BLU
import Data.Either
import Data.ByteString.Lazy as BL
import Data.Text.Lazy as TL
import Data.Text.Lazy.Encoding as TLE
import Data.Text.Encoding as TSE


incr = do id <- get
          put $ id + 1
          return $ id

foo = do foo <- incr
         x <- incr
         return (foo,x)

bla = runState foo 0

data Test = Test { name :: String, fileQuota :: Int }

instance FromRow Test where
  fromRow = Test <$> field <*> field

testdb :: (FromRow (Row r), Fields r, LensQueryable t r p) => Lens t r p fds -> IO ()
testdb (l :: Lens t r p fds) = do
  conn <- connect defaultConnectInfo {
    connectDatabase = "links",
    connectUser = "links",
    connectPassword = "links"
  }
  let lft f arg = build "{}" <$> Only <$> BLU.toString <$> fromRight "error" <$> f conn (BLU.fromString arg)
  let db = (lft escapeIdentifier, lft escapeStringConn)
  q <- build_query db l
  mapM_ Prelude.print =<< (query_ conn (Query { fromQuery = BL.toStrict $ TLE.encodeUtf8 $ toLazyText q}) :: IO [Row r])
  --return q
  --mapM_ print =<< (query_ conn "select 2 + 2 as foo, 'hello' as bla" :: IO [Row '[ '( "A", 'Types.Int), '("B", 'Types.String)]])
