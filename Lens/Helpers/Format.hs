{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             AllowAmbiguousTypes, TypeApplications, OverloadedStrings #-}

module Lens.Helpers.Format where

import Data.Text.Format(build, Only(..))
import Data.Text.Lazy.Builder(Builder)
import Data.Text.Buildable(Buildable)

build_sep :: (Buildable sep, Buildable a) => sep -> [a] -> Builder
build_sep _ [] = build "" ()
build_sep _ [x] = build "{}" (Only x)
build_sep sep (x : xs) = build "{}{}{}" (x, sep, build_sep sep xs)

build_sep_str :: Buildable a => String -> [a] -> Builder
build_sep_str sep xs = build_sep sep xs

build_sep_comma :: Buildable a => [a] -> Builder
build_sep_comma = build_sep_str ", "

build_sep_space :: Buildable a => [a] -> Builder
build_sep_space = build_sep_str ", "
