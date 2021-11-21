#!/bin/sh

ghc -XDataKinds -XOverloadedLabels -XTypeOperators -XGADTs -XTypeFamilies -XPolyKinds -XKindSignatures -XFlexibleInstances -XMultiParamTypeClasses -XTypeApplications -XAllowAmbiguousTypes -XOverloadedStrings -XFlexibleContexts -XUndecidableInstances -dynamic -O2 Benchmark.hs
