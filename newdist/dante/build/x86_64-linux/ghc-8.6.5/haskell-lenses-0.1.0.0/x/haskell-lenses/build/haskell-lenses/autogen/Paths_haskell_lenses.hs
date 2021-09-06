{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_haskell_lenses (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/administrator/.cabal/bin"
libdir     = "/home/administrator/.cabal/lib/x86_64-linux-ghc-8.6.5/haskell-lenses-0.1.0.0-inplace-haskell-lenses"
dynlibdir  = "/home/administrator/.cabal/lib/x86_64-linux-ghc-8.6.5"
datadir    = "/home/administrator/.cabal/share/x86_64-linux-ghc-8.6.5/haskell-lenses-0.1.0.0"
libexecdir = "/home/administrator/.cabal/libexec/x86_64-linux-ghc-8.6.5/haskell-lenses-0.1.0.0"
sysconfdir = "/home/administrator/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "haskell_lenses_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "haskell_lenses_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "haskell_lenses_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "haskell_lenses_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "haskell_lenses_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "haskell_lenses_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
