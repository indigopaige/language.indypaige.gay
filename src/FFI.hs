module FFI (mkEnvAlloc, mkEnvStore, mkEnvLoad, mkMakeClosure, mkClosureFunction, mkClosureEnvironment, importFn) where

import Foreign.Ptr
import Data.Word
import Runtime

type Fn = Word64 -> Word64 -> IO Word64

type EnvAlloc = Word64 -> IO Word64
type EnvStore = Word64 -> Word64 -> Word64 -> IO ()
type EnvLoad = Word64 -> Word64 -> IO Word64
type MakeClosure = Word64 -> Word64 -> IO Word64
type ClosureFunction = Word64 -> IO Word64
type ClosureEnvironment = Word64 -> IO Word64

foreign import ccall "wrapper"
  mkEnvAlloc :: EnvAlloc -> IO (FunPtr EnvAlloc)

foreign import ccall "wrapper"
  mkEnvStore :: EnvStore -> IO (FunPtr EnvStore)

foreign import ccall "wrapper"
  mkEnvLoad :: EnvLoad -> IO (FunPtr EnvLoad)

foreign import ccall "wrapper"
  mkMakeClosure :: MakeClosure -> IO (FunPtr MakeClosure)

foreign import ccall "wrapper"
  mkClosureFunction :: ClosureFunction -> IO (FunPtr ClosureFunction)

foreign import ccall "wrapper"
  mkClosureEnvironment :: ClosureEnvironment -> IO (FunPtr ClosureEnvironment)

foreign import ccall "dynamic"
  importFn :: FunPtr Fn -> Fn
