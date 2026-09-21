module Language where

import qualified Type.Base.Proxy as T
import Control.Exception (bracket)
import Control.Monad.IO.Class
import Data.Text (Text, pack)
import Text.Parse
import Text.Infer
import Text.Build
import Data.Token
import LLVM.Core
import Data.Word
import Data.Ast
import Compile

import LLVM.ExecutionEngine
import Runtime
import Foreign.Ptr (FunPtr, nullFunPtr, freeHaskellFunPtr)
import FFI

withRuntimePtrs :: (RuntimePtrs -> IO a) -> IO a
withRuntimePtrs =
  bracket allocRuntimePtrs freeRuntimePtrs
  where
    allocRuntimePtrs = do
      envAllocPtr'           <- mkEnvAlloc envAlloc
      envStorePtr'           <- mkEnvStore envStore
      envLoadPtr'            <- mkEnvLoad envLoad
      makeClosurePtr'        <- mkMakeClosure makeClosure
      closureFunctionPtr'    <- mkClosureFunction closureFunction
      closureEnvironmentPtr' <- mkClosureEnvironment closureEnvironment

      pure RuntimePtrs
        { envAllocPtr           = envAllocPtr'
        , envStorePtr           = envStorePtr'
        , envLoadPtr            = envLoadPtr'
        , makeClosurePtr        = makeClosurePtr'
        , closureFunctionPtr    = closureFunctionPtr'
        , closureEnvironmentPtr = closureEnvironmentPtr'
        }

    freeRuntimePtrs runtime = do
      freeHaskellFunPtr (envAllocPtr runtime)
      freeHaskellFunPtr (envStorePtr runtime)
      freeHaskellFunPtr (envLoadPtr runtime)
      freeHaskellFunPtr (makeClosurePtr runtime)
      freeHaskellFunPtr (closureFunctionPtr runtime)
      freeHaskellFunPtr (closureEnvironmentPtr runtime)

compile :: Text -> IO (Maybe Word64)
compile x = do
  parsed <- run x

  case parsed of
    Nothing ->
      pure Nothing

    Just (body, functions) ->
      withRuntimePtrs $ \runtime -> do
        module_ <- newModule

        built <- defineModule module_ $
          buildModule body functions runtime

        case built of
          Left err ->
            print err >> pure Nothing

          Right (_compiled, _applyFn, entryFn, runtimeFns) -> do
            result <- runEngineAccessWithModule module_ $ do
              addFunctionValue (rfEnvAlloc runtimeFns) (envAllocPtr runtime)

              addFunctionValue (rfEnvStore runtimeFns) (envStorePtr runtime)

              addFunctionValue (rfEnvLoad runtimeFns) (envLoadPtr runtime)

              addFunctionValue (rfMakeClosure runtimeFns) (makeClosurePtr runtime)

              addFunctionValue (rfClosureFunction runtimeFns) (closureFunctionPtr runtime)

              addFunctionValue (rfClosureEnvironment runtimeFns) (closureEnvironmentPtr runtime)

              entry <- generateFunction entryFn

              liftIO entry

            pure (Just result)

run :: Text -> IO (Maybe (Exp Build, Functions))
run x =
  case p of
    Left e -> print e >> pure Nothing

    Right parsed ->
      let infer = expParseToInfer parsed
      in case inferTy infer of
           Left e ->
             print e >> pure Nothing

           Right _ ->
             case runConvert (reduce infer) of
               Left e -> print e >> pure Nothing
               Right z -> pure (Just z)

  where
    p = parseTokenStream expr keywords "test" x
