module Data.Functions where

import Data.Word

type Fn = Word64 -> Word64 -> IO Word64

type ClosureEnvironment = Word64 -> IO Word64
type ClosureFunction    = Word64 -> IO Word64
type MakeClosure        = Word64 -> Word64 -> IO Word64

type EnvAlloc           = Word64 -> IO Word64
type EnvStore           = Word64 -> Word64 -> Word64 -> IO ()
type EnvLoad            = Word64 -> Word64 -> IO Word64
