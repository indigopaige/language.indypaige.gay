module Compile where

import qualified Data.Text as Text
import qualified Data.Map as Map
import Effectful.Reader.Static
import Effectful.Error.Static
import Foreign.Ptr (FunPtr)
import Data.Text (Text)
import Data.Map (Map)
import Data.Functions
import Control.Monad
import Effectful
import LLVM.Core
import Data.Word
import Data.List
import Data.Ast
import Data.Int

data CodegenError
  = InvalidVariable Name
  | UnknownBuiltin Text
  | MissingFunction Int
  | OutOfScopeVar Name
  | LetSurvival Span
  | MissingSlot Int
  | NoArithmetic Ty
  | OutOfBounds
  deriving Show

type Codegen es =
  ( Error CodegenError :> es
  , Reader CompileEnv :> es
  )

type Recipe      = CGEnv -> CodeGenFunction Word64 Boxed

type Functions   = Map Int (Exp Build)
type Entry       = IO Word64
type Boxed       = Value Word64

class Gen a where
  codegen :: Codegen es => a -> Eff es Recipe

instance Gen (Lit Build) where
  codegen (Unsigned _ w) = pure $ \_ -> pure $ valueOf (fromIntegral w :: Word64)
  codegen (Decimal  _ d) = pure $ \_ -> bitcast (valueOf d)
  codegen (Boolean  _ b) = pure $ \_ -> zext (valueOf b)
  codegen (Signed   _ i) = pure $ \_ -> bitcast $ valueOf (fromIntegral i :: Int64)

data RuntimeFunctions = RuntimeFunctions
  { rfEnvAlloc           :: Function EnvAlloc
  , rfEnvStore           :: Function EnvStore
  , rfEnvLoad            :: Function EnvLoad
  , rfMakeData           :: Function MakeData
  , rfMakeClosure        :: Function MakeClosure
  , rfDataEnvironment    :: Function DataEnvironment
  , rfClosureFunction    :: Function ClosureFunction
  , rfClosureEnvironment :: Function ClosureEnvironment
  }

data RuntimePtrs = RuntimePtrs
  { envAllocPtr           :: FunPtr EnvAlloc
  , envStorePtr           :: FunPtr EnvStore
  , envLoadPtr            :: FunPtr EnvLoad
  , makeDataPtr           :: FunPtr MakeData
  , makeClosurePtr        :: FunPtr MakeClosure
  , dataEnvironmentPtr    :: FunPtr DataEnvironment
  , closureFunctionPtr    :: FunPtr ClosureFunction
  , closureEnvironmentPtr :: FunPtr ClosureEnvironment
  }

data CompileEnv = CompileEnv
  { ceEntry     :: Bool
  , ceFunctions :: Map Int (Function Fn)
  , ceRuntime   :: RuntimeFunctions
  }

mkCompileEnv :: Bool -> Map Int (Function Fn) -> RuntimeFunctions -> CompileEnv
mkCompileEnv isEntry functions runtime =
  CompileEnv
    { ceEntry     = isEntry
    , ceFunctions = functions
    , ceRuntime   = runtime
    }

runCompileWith
  :: CompileEnv
  -> Eff '[Reader CompileEnv, Error CodegenError] a
  -> Either CodegenError a
runCompileWith env action =
  runPureEff . runErrorNoCallStack . runReader env $ action

data CGEnv = CGEnv
  { cgArg :: Boxed
  , cgEnv :: Boxed
  , cgApp :: Function Fn
  }

getCompiledFunction
  :: Codegen es
  => Int
  -> Eff es (Function Fn)
getCompiledFunction i = do
  functions <- asks ceFunctions

  case Map.lookup i functions of
    Just function ->
      pure function

    Nothing ->
      throwError (MissingFunction i)

compileEq :: Boxed -> Boxed -> CodeGenFunction r Boxed
compileEq lhs rhs = cmp CmpEQ lhs rhs >>= zext

buildData
  :: Function EnvAlloc
  -> Function EnvStore
  -> Function MakeData
  -> TypeId
  -> Int
  -> [Boxed]
  -> CodeGenFunction r Boxed

buildData allocFn storeFn makeDataFn (TypeId typeId) tag fields = do
  environment <-
    runCall $
      applyCall
        (callFromFunction allocFn)
        (valueOf $ fromIntegral (length fields) :: Value Word64)

  forM_ (zip [0..] fields) $ \(i, field) ->
    runCall $
      applyCall
        (applyCall
          (applyCall
            (callFromFunction storeFn)
            environment)
          (valueOf $ fromIntegral i :: Value Word64))
        field

  runCall $
    applyCall
      (applyCall
        (applyCall
          (callFromFunction makeDataFn)
          (valueOf $ fromIntegral typeId :: Value Word64))
        (valueOf $ fromIntegral tag :: Value Word64))
      environment

compileBinOp :: Codegen es => Text -> Ty -> Eff es (Boxed -> Boxed -> CodeGenFunction r Boxed)
compileBinOp name ty = case ty of
  TyNum -> intOp
  TyWrd -> wrdOp
  TyDec -> decOp
  _     -> throwError $ NoArithmetic ty
  where
    wrdOp = dispatch name [ ("addWrd", add)
                          , ("subWrd", sub)
                          , ("mulWrd", mul)
                          , ("divWrd", idiv)]

    decOp = do
      op <- dispatch name [ ("addDec", fadd)
                          , ("subDec", fsub)
                          , ("mulDec", fmul)
                          , ("divDec", fdiv)]
      pure $ \lhs rhs -> do
        x <- bitcast lhs :: CodeGenFunction r (Value Double)
        y <- bitcast rhs :: CodeGenFunction r (Value Double)
        r <- op x y
        bitcast r

    intOp = do
      op <- dispatch name [ ("addNum", add)
                          , ("subNum", sub)
                          , ("mulNum", mul)
                          , ("divNum", idiv)]
      pure $ \lhs rhs -> do
        x <- bitcast lhs :: CodeGenFunction r (Value Int64)
        y <- bitcast rhs :: CodeGenFunction r (Value Int64)
        r <- op x y
        bitcast r

dispatch
  :: Codegen es
  => Text
  -> [(Text, a -> a -> CodeGenFunction r a)]
  -> Eff es (a -> a -> CodeGenFunction r a)
dispatch name table =
  case lookup name table of
    Just op -> pure op
    Nothing -> throwError $ UnknownBuiltin name

loadEnv :: Function EnvLoad -> Boxed -> Int -> CodeGenFunction r Boxed
loadEnv loadFn env i = do
  runCall $
    applyCall (applyCall (callFromFunction loadFn) env)
      (valueOf (fromIntegral i :: Word64))

buildClosure
  :: Function EnvAlloc
  -> Function EnvStore
  -> Function MakeClosure
  -> Int
  -> [Boxed]
  -> CodeGenFunction r Boxed
buildClosure allocFn storeFn mkClosureFn functionId values = do
  environment <- runCall $
    applyCall
      (callFromFunction allocFn)
      (valueOf (fromIntegral (length values) :: Word64))

  forM_ (zip [0..] values) $ \(i, value) ->
    runCall $
      applyCall
        (applyCall
          (applyCall (callFromFunction storeFn) environment)
          (valueOf (fromIntegral i :: Word64)))
        value

  runCall $
    applyCall
      (applyCall
        (callFromFunction mkClosureFn)
        (valueOf (fromIntegral functionId :: Word64)))
      environment

compileBranch
  :: CodeGenFunction r Boxed
  -> CodeGenFunction r Boxed
  -> CodeGenFunction r Boxed
  -> CodeGenFunction r Boxed
compileBranch condition onTrue onFalse = do
  cv   <- condition
  cond <- trunc cv :: CodeGenFunction r (Value Bool)

  tblk <- newBasicBlock
  eblk <- newBasicBlock
  jblk <- newBasicBlock

  condBr cond tblk eblk

  defineBasicBlock tblk
  tval <- onTrue
  tend <- getCurrentBasicBlock
  br jblk

  defineBasicBlock eblk
  eval <- onFalse
  eend <- getCurrentBasicBlock
  br jblk

  defineBasicBlock jblk

  phi [(tval, tend), (eval, eend)]

instance Gen (Exp Build) where
  codegen = \case
    Exp _ (DataBuild tid tag fields) -> do
      fieldRecipes <- traverse codegen fields

      allocFn <- asks @CompileEnv $ rfEnvAlloc . ceRuntime

      storeFn <- asks @CompileEnv $ rfEnvStore . ceRuntime

      makeDataFn <- asks @CompileEnv $ rfMakeData . ceRuntime

      pure $ \env -> do
        values <- traverse (\recipe -> recipe env) fieldRecipes

        buildData allocFn storeFn makeDataFn tid tag values

    Acc _ ref x -> do
      rx <- codegen x

      dataEnvFn <- asks @CompileEnv $ rfDataEnvironment . ceRuntime

      loadFn <- asks @CompileEnv $ rfEnvLoad . ceRuntime

      pure $ \env -> do
        value <- rx env

        fields <- runCall $ applyCall (callFromFunction dataEnvFn) value

        loadEnv loadFn fields (fieldIndex ref)

    Exp _ (Env i) -> do
      isEntry <- asks ceEntry

      if isEntry
        then throwError (MissingSlot i)
        else do
          ptr <- asks @CompileEnv (rfEnvLoad . ceRuntime)
          pure $ \env -> loadEnv ptr (cgEnv env) i

    Lit _ () lit -> codegen lit

    Exp _ (OutOfScope n) -> throwError (OutOfScopeVar n)

    Exp _ Arg -> do
      isEntry <- asks ceEntry
      if isEntry
        then throwError OutOfBounds
        else pure $ \env -> pure (cgArg env)

    Var _ (x, _) -> throwError (InvalidVariable x)

    Let s _ _ _ -> throwError (LetSurvival s)

    App _ () (App _ () (Exp _ (OutOfScope (Name opName _))) lhsExp) rhsExp
      | opName == "eq" -> do
          rl <- codegen lhsExp
          rr <- codegen rhsExp

          pure $ \e -> do
            lv <- rl e
            rv <- rr e
            compileEq lv rv

      | Just ty <- opType opName -> do
          rl <- codegen lhsExp
          rr <- codegen rhsExp
          op <- compileBinOp opName ty

          pure $ \env -> do
            lv <- rl env
            rv <- rr env
            op lv rv

      | otherwise -> throwError $ UnknownBuiltin opName

    App _ () f x -> do
      rf <- codegen f
      rx <- codegen x

      pure $ \env -> do
        fv <- rf env
        xv <- rx env

        runCall $ applyCall (applyCall (callFromFunction (cgApp env)) fv) xv

    Exp _ (Closure functionId captures) -> do
      captureRecipes <- traverse codegen captures
      allocFn        <- asks @CompileEnv (rfEnvAlloc . ceRuntime)
      storeFn        <- asks @CompileEnv (rfEnvStore . ceRuntime)
      mkClosureFn    <- asks @CompileEnv (rfMakeClosure . ceRuntime)

      pure $ \env -> do
        values <- traverse (\recipe -> recipe env) captureRecipes
        buildClosure allocFn storeFn mkClosureFn functionId values

    Cnd _ () x y z -> do
      rc <- codegen x
      ry <- codegen y
      rn <- codegen z

      pure $ \env ->
        compileBranch (rc env) (ry env) (rn env)

compileEntry
  :: Exp Build
  -> Map Int (Function Fn)
  -> RuntimeFunctions
  -> Either CodegenError Recipe
compileEntry body functions runtime =
  runCompileWith (mkCompileEnv True functions runtime) (codegen body)

compileRecipe
  :: Exp Build
  -> Map Int (Function Fn)
  -> RuntimeFunctions
  -> Either CodegenError Recipe
compileRecipe body functions runtime =
  runCompileWith (mkCompileEnv False functions runtime) (codegen body)

declareFunctions
  :: Functions
  -> CodeGenModule (Map Int (Function Fn))
declareFunctions =
  Map.traverseWithKey $ \functionId _ ->
    newNamedFunction
      ExternalLinkage
      ("function_" ++ show functionId)

compileRecipes
  :: Functions
  -> Map Int (Function Fn)
  -> RuntimeFunctions
  -> Either CodegenError (Map Int Recipe)
compileRecipes functions compiled runtime =
  Map.traverseWithKey compileOne functions
  where
    compileOne _ body =
      compileRecipe body compiled runtime

defineCompiledFunction
  :: Function Fn
  -> Recipe
  -> Function Fn
  -> CodeGenModule ()
defineCompiledFunction function recipe applyFn =
  defineFunction function $ \environment argument -> do
    let cgEnv =
          CGEnv
            { cgArg = argument
            , cgEnv = environment
            , cgApp = applyFn
            }

    result <- recipe cgEnv
    ret result

defineApply
  :: Map Int (Function Fn)
  -> Function ClosureFunction
  -> Function ClosureEnvironment
  -> CodeGenModule (Function Fn)
defineApply functions closureFunctionFn closureEnvironmentFn = do
  applyFn <-
    newNamedFunction
      ExternalLinkage
      "apply"

  defineFunction applyFn $ \closure argument -> do
    functionId <-
      runCall $
        applyCall
          (callFromFunction closureFunctionFn)
          closure

    environment <-
      runCall $
        applyCall
          (callFromFunction closureEnvironmentFn)
          closure

    result <-
      dispatchApply
        (Map.toAscList functions)
        functionId
        environment
        argument

    ret result

  pure applyFn

dispatchApply
  :: [(Int, Function Fn)]
  -> Boxed
  -> Boxed
  -> Boxed
  -> CodeGenFunction r Boxed
dispatchApply functions functionId environment argument = do
  done <- newBasicBlock

  resultBlocks <- go done functions

  defineBasicBlock done

  phi resultBlocks

  where
    go
      :: BasicBlock
      -> [(Int, Function Fn)]
      -> CodeGenFunction r [(Value Word64, BasicBlock)]

    go _ [] = do
      unreachable
      pure []

    go done ((functionId', function) : rest) = do
      body <- newBasicBlock
      next <- newBasicBlock

      comparison <-
        cmp
          CmpEQ
          functionId
          (valueOf (fromIntegral functionId' :: Word64))

      condBr comparison body next

      defineBasicBlock body

      result <-
        runCall $
          applyCall
            (applyCall
              (callFromFunction function)
              environment)
            argument

      bodyEnd <- getCurrentBasicBlock
      br done

      defineBasicBlock next

      restResults <- go done rest

      pure
        ((result, bodyEnd) : restResults)

buildModule
  :: Exp Build
  -> Functions
  -> CodeGenModule
       (Either CodegenError
         ( Map Int (Function Fn)
         , Function Fn
         , Function Entry
         , RuntimeFunctions
         ))
buildModule body functions = do
  runtimeFns <- declareRuntimeFunctions

  compiled <- declareFunctions functions

  case compileRecipes functions compiled runtimeFns of
    Left err ->
      pure (Left err)

    Right recipes -> do
      applyFn <-
        defineApply
          compiled
          (rfClosureFunction runtimeFns)
          (rfClosureEnvironment runtimeFns)

      forM_ (Map.toList recipes) $ \(functionId, recipe) -> do
        let function = compiled Map.! functionId

        defineCompiledFunction
          function
          recipe
          applyFn

      case compileEntry body compiled runtimeFns of
        Left err ->
          pure (Left err)

        Right entryRecipe -> do
          entryFn <- defineEntry applyFn entryRecipe

          pure
            (Right
              (compiled, applyFn, entryFn, runtimeFns))

defineEntry :: Function Fn -> Recipe -> CodeGenModule (Function Entry)
defineEntry applyFn recipe = do
  entryFn <- newNamedFunction ExternalLinkage "entry"

  defineFunction entryFn $ do
    result <- recipe CGEnv
      { cgArg = valueOf 0
      , cgEnv = valueOf 0
      , cgApp = applyFn
      }

    ret result

  pure entryFn

declareRuntimeFunctions :: CodeGenModule RuntimeFunctions
declareRuntimeFunctions = do
  envAlloc <-
    newNamedFunction ExternalLinkage "env_alloc"
      :: CodeGenModule (Function EnvAlloc)

  envStore <-
    newNamedFunction ExternalLinkage "env_store"
      :: CodeGenModule (Function EnvStore)

  envLoad <-
    newNamedFunction ExternalLinkage "env_load"
      :: CodeGenModule (Function EnvLoad)

  makeClosure <-
    newNamedFunction ExternalLinkage "make_closure"
      :: CodeGenModule (Function MakeClosure)

  closureFunction <-
    newNamedFunction ExternalLinkage "closure_function"
      :: CodeGenModule (Function ClosureFunction)

  closureEnvironment <-
    newNamedFunction ExternalLinkage "closure_environment"
      :: CodeGenModule (Function ClosureEnvironment)

  dataEnvironment <-
    newNamedFunction ExternalLinkage "data_environment"
      :: CodeGenModule (Function DataEnvironment)

  makeData <-
    newNamedFunction ExternalLinkage "make_data"
      :: CodeGenModule (Function MakeData)

  pure RuntimeFunctions
    { rfEnvAlloc = envAlloc
    , rfEnvStore = envStore
    , rfEnvLoad = envLoad
    , rfMakeData = makeData
    , rfMakeClosure = makeClosure
    , rfDataEnvironment = dataEnvironment
    , rfClosureFunction = closureFunction
    , rfClosureEnvironment = closureEnvironment
    }
