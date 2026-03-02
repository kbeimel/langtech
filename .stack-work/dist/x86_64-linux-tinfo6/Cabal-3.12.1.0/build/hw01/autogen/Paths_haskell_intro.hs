{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
#if __GLASGOW_HASKELL__ >= 810
{-# OPTIONS_GHC -Wno-prepositive-qualified-module #-}
#endif
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_haskell_intro (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
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

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath




bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/home/kaybe/langtech/.stack-work/install/x86_64-linux-tinfo6/5e72ac7fd62b629e689cdd1f9bd092b474cba6a72bfa6c97894c2ae7c0dc51ef/9.10.3/bin"
libdir     = "/home/kaybe/langtech/.stack-work/install/x86_64-linux-tinfo6/5e72ac7fd62b629e689cdd1f9bd092b474cba6a72bfa6c97894c2ae7c0dc51ef/9.10.3/lib/x86_64-linux-ghc-9.10.3-56e0/haskell-intro-0.1.0.0-4uUr0YtL9mQAWAVNLj0gtW-hw01"
dynlibdir  = "/home/kaybe/langtech/.stack-work/install/x86_64-linux-tinfo6/5e72ac7fd62b629e689cdd1f9bd092b474cba6a72bfa6c97894c2ae7c0dc51ef/9.10.3/lib/x86_64-linux-ghc-9.10.3-56e0"
datadir    = "/home/kaybe/langtech/.stack-work/install/x86_64-linux-tinfo6/5e72ac7fd62b629e689cdd1f9bd092b474cba6a72bfa6c97894c2ae7c0dc51ef/9.10.3/share/x86_64-linux-ghc-9.10.3-56e0/haskell-intro-0.1.0.0"
libexecdir = "/home/kaybe/langtech/.stack-work/install/x86_64-linux-tinfo6/5e72ac7fd62b629e689cdd1f9bd092b474cba6a72bfa6c97894c2ae7c0dc51ef/9.10.3/libexec/x86_64-linux-ghc-9.10.3-56e0/haskell-intro-0.1.0.0"
sysconfdir = "/home/kaybe/langtech/.stack-work/install/x86_64-linux-tinfo6/5e72ac7fd62b629e689cdd1f9bd092b474cba6a72bfa6c97894c2ae7c0dc51ef/9.10.3/etc"

getBinDir     = catchIO (getEnv "haskell_intro_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "haskell_intro_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "haskell_intro_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "haskell_intro_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "haskell_intro_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "haskell_intro_sysconfdir") (\_ -> return sysconfdir)



joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'
