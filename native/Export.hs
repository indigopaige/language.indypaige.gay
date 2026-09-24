module Export () where

import Data.Word
import Runtime

foreign export ccall "env_alloc"
  envAlloc :: Word64 -> IO Word64

foreign export ccall "env_store"
  envStore :: Word64 -> Word64 -> Word64 -> IO ()

foreign export ccall "env_load"
  envLoad :: Word64 -> Word64 -> IO Word64

foreign export ccall "make_closure"
  makeClosure :: Word64 -> Word64 -> IO Word64

foreign export ccall "closure_function"
  closureFunction :: Word64 -> IO Word64

foreign export ccall "closure_environment"
  closureEnvironment :: Word64 -> IO Word64
