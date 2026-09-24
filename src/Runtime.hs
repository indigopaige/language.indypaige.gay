module Runtime where

import Data.Array.IO
import Data.Word
import Foreign.Ptr
import Foreign.StablePtr

type Handle = Word64

data Env = Env
  { envValues :: IOUArray Int Word64
  }

data Closure = Closure
  { closureFunctionId :: Word64
  , closureEnvironment' :: Handle
  }

data DataValue = DataValue
  { dataTypeId       :: Word64
  , dataTag          :: Word64
  , dataEnvironment' :: Handle
  }

makeData
  :: Word64
  -> Word64
  -> Handle
  -> IO Handle

makeData typeId tag environment = do
  ptr <-
    newStablePtr $
      DataValue
        { dataTypeId       = typeId
        , dataTag          = tag
        , dataEnvironment' = environment
        }

  pure $
    handleOf ptr

dataType :: Handle -> IO Word64
dataType handle = do
  value <-
    deRefStablePtr $
      stablePtrOf handle

  pure $
    dataTypeId value


dataConstructor :: Handle -> IO Word64
dataConstructor handle = do
  value <-
    deRefStablePtr $
      stablePtrOf handle

  pure $
    dataTag value


dataEnvironment :: Handle -> IO Handle
dataEnvironment handle = do
  value <-
    deRefStablePtr $
      stablePtrOf handle

  pure $
    dataEnvironment' value

handleOf :: StablePtr a -> Handle
handleOf =
  fromIntegral . ptrToWordPtr . castStablePtrToPtr

stablePtrOf :: Handle -> StablePtr a
stablePtrOf =
  castPtrToStablePtr . wordPtrToPtr . fromIntegral

envAlloc :: Word64 -> IO Handle
envAlloc n = do
  let size = max 1 (fromIntegral n)

  values <- newArray (0, size - 1) 0

  ptr <- newStablePtr (Env values)

  pure $ handleOf ptr

envStore :: Handle -> Word64 -> Word64 -> IO ()
envStore handle index value = do
  Env values <- deRefStablePtr (stablePtrOf handle)

  writeArray values (fromIntegral index) value

envLoad :: Handle -> Word64 -> IO Word64
envLoad handle index = do
  Env values <- deRefStablePtr (stablePtrOf handle)

  readArray values (fromIntegral index)

envFree :: Handle -> IO ()
envFree handle =
  freeStablePtr (stablePtrOf handle)


makeClosure :: Word64 -> Handle -> IO Handle
makeClosure functionId environment = do
  ptr <- newStablePtr
    Closure
      { closureFunctionId = functionId
      , closureEnvironment' = environment
      }

  pure $ handleOf ptr

closureFunction :: Handle -> IO Word64
closureFunction handle = do
  closure <- deRefStablePtr (stablePtrOf handle)
  pure $ closureFunctionId closure

closureEnvironment :: Handle -> IO Word64
closureEnvironment handle = do
  closure <- deRefStablePtr (stablePtrOf handle)
  pure $ closureEnvironment' closure

closureFree :: Handle -> IO ()
closureFree handle = do
  closure <- deRefStablePtr (stablePtrOf handle)

  envFree (closureEnvironment' closure)

  freeStablePtr (stablePtrOf handle)

