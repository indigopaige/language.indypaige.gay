module Language where

import qualified Data.Text.IO as Text
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
import Foreign.StablePtr
import FFI

withRuntimePtrs :: (RuntimePtrs -> IO a) -> IO a
withRuntimePtrs =
  bracket allocRuntimePtrs freeRuntimePtrs
  where
    allocRuntimePtrs = do
      envAllocPtr'           <- mkEnvAlloc envAlloc
      envStorePtr'           <- mkEnvStore envStore
      envLoadPtr'            <- mkEnvLoad envLoad
      makeDataPtr'           <- mkMakeData makeData
      makeClosurePtr'        <- mkMakeClosure makeClosure
      dataEnvironmentPtr'    <- mkDataEnvironment dataEnvironment
      closureFunctionPtr'    <- mkClosureFunction closureFunction
      closureEnvironmentPtr' <- mkClosureEnvironment closureEnvironment

      pure RuntimePtrs
        { envAllocPtr           = envAllocPtr'
        , envStorePtr           = envStorePtr'
        , envLoadPtr            = envLoadPtr'
        , makeDataPtr           = makeDataPtr'
        , makeClosurePtr        = makeClosurePtr'
        , dataEnvironmentPtr    = dataEnvironmentPtr'
        , closureFunctionPtr    = closureFunctionPtr'
        , closureEnvironmentPtr = closureEnvironmentPtr'
        }

    freeRuntimePtrs runtime = do
      freeHaskellFunPtr (envAllocPtr runtime)
      freeHaskellFunPtr (envStorePtr runtime)
      freeHaskellFunPtr (envLoadPtr runtime)
      freeHaskellFunPtr (makeDataPtr runtime)
      freeHaskellFunPtr (makeClosurePtr runtime)
      freeHaskellFunPtr (closureFunctionPtr runtime)
      freeHaskellFunPtr (closureEnvironmentPtr runtime)

dataType :: Handle -> IO Word64
dataType handle = do
  value <- deRefStablePtr $ stablePtrOf handle
  pure $ dataTypeId value

dataConstructor :: Handle -> IO Word64
dataConstructor handle = do
  value <- deRefStablePtr $ stablePtrOf handle
  pure $ dataTag value

dataField :: Handle -> Word64 -> IO Word64
dataField handle index = do
  value <- deRefStablePtr $ stablePtrOf handle
  envLoad (dataEnvironment' value) index

compile :: Text -> IO (Maybe Word64)
compile x = do
  parsed <- run x

  case parsed of
    Nothing ->
      pure Nothing

    Just (body, functions, typeDefs) ->
      withRuntimePtrs $ \runtime -> do
        module_ <- newModule

        built <- defineModule module_ $
          buildModule body functions

        case built of
          Left err ->
            print err >> pure Nothing

          Right (_compiled, _applyFn, entryFn, runtimeFns) -> do
            result <- runEngineAccessWithModule module_ $ do
              addFunctionValue (rfEnvAlloc runtimeFns) (envAllocPtr runtime)

              addFunctionValue (rfEnvStore runtimeFns) (envStorePtr runtime)

              addFunctionValue (rfEnvLoad runtimeFns) (envLoadPtr runtime)

              addFunctionValue (rfMakeData runtimeFns) (makeDataPtr runtime)

              addFunctionValue (rfMakeClosure runtimeFns) (makeClosurePtr runtime)

              addFunctionValue (rfDataEnvironment runtimeFns) (dataEnvironmentPtr runtime)

              addFunctionValue (rfClosureFunction runtimeFns) (closureFunctionPtr runtime)

              addFunctionValue (rfClosureEnvironment runtimeFns) (closureEnvironmentPtr runtime)

              entry <- generateFunction entryFn

              liftIO entry

            pure (Just result)

run :: Text -> IO (Maybe (Exp Build, Functions, TypeDefs))
run x =
  case p of
    Left e ->
      print e >> pure Nothing

    Right parsed ->
      case expParseToInfer parsed of
        Left e ->
          print e >> pure Nothing

        Right (infer, typeDefs) ->
          case inferTy infer of
            Left e ->
              print e >> pure Nothing

            Right _ ->
              case runConvert (reduce infer) of
                Left e ->
                  print e >> pure Nothing

                Right (body, functions) ->
                  pure $ Just (body, functions, typeDefs)

  where
    p =
      parseTokenStream expr keywords "test" x

compileFile :: FilePath -> FilePath -> IO Bool
compileFile input output = do
  source <- Text.readFile input
  result <- run source

  case result of
    Nothing ->
      pure False

    Just (body, functions, _typeDefs) -> do
      module_ <- newModule

      built <-
        defineModule module_ $
          buildModule body functions

      case built of
        Left err -> do
          print err
          pure False

        Right _ -> do
          writeBitcodeToFile output module_
          pure True
