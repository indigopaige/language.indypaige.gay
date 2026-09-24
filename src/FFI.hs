module FFI  where

import Data.Functions
import Foreign.Ptr
import Data.Word
import Runtime

foreign import ccall "wrapper" mkClosureEnvironment :: ClosureEnvironment -> IO (FunPtr ClosureEnvironment)
foreign import ccall "wrapper" mkDataEnvironment    :: DataEnvironment -> IO (FunPtr DataEnvironment)
foreign import ccall "wrapper" mkClosureFunction    :: ClosureFunction -> IO (FunPtr ClosureFunction)
foreign import ccall "wrapper" mkMakeClosure        :: MakeClosure -> IO (FunPtr MakeClosure)
foreign import ccall "wrapper" mkEnvAlloc           :: EnvAlloc -> IO (FunPtr EnvAlloc)
foreign import ccall "wrapper" mkEnvStore           :: EnvStore -> IO (FunPtr EnvStore)
foreign import ccall "wrapper" mkMakeData           :: MakeData -> IO (FunPtr MakeData)
foreign import ccall "wrapper" mkEnvLoad            :: EnvLoad -> IO (FunPtr EnvLoad)
foreign import ccall "dynamic" importFn             :: FunPtr Fn -> Fn
