{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module PackageInfo_haskell_intro (
    name,
    version,
    synopsis,
    copyright,
    homepage,
  ) where

import Data.Version (Version(..))
import Prelude

name :: String
name = "haskell_intro"
version :: Version
version = Version [0,1,0,0] []

synopsis :: String
synopsis = "Intro Haskell Homework for CMSC 433, UMD"
copyright :: String
copyright = ""
homepage :: String
homepage = ""
