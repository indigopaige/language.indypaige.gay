module Text.Build where

import Effectful.State.Static.Local
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Set as Set
import Effectful.Reader.Static
import Effectful.Reader.Static
import Effectful.Error.Static
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad
import Control.Lens
import Data.Coerce
import Effectful
import Data.List
import Data.Ast

shift :: Int -> Int -> Exp Infer -> Exp Infer
shift d c (Let span () x y) = Let span () (shift d (c + 1) x) $ shift d (c + 1) y

shift d c (Abs span () e)   = Abs span () $ shift d (c + 1) e

shift d c e@(Var span (x, n))
  | n >= c                  = Var span (x, (n + d))
  | otherwise               = e

shift d c e                 = e & plate %~ shift d c

subst :: Int -> Exp Infer -> Exp Infer -> Exp Infer
subst j s = f 0
  where
    f d e = g e
      where
        g (Let span () x y) = Let span () (f (d + 1) x) (f (d + 1) y)

        g (Abs span () x)   = Abs span () (f (d + 1) x)
        
        g lam@(Var span (_, k))
          | k == j + d      = shift d 0 s
          | otherwise       = lam

        g x                 = x & plate %~ g

beta :: Exp Infer -> Exp Infer -> Exp Infer
beta x y = shift (-1) 0 $ subst 0 (shift 1 0 x) y



reduce :: Exp Infer -> Exp Infer
reduce (Let _ () t@(Typ _ _ _) body) = reduce $ beta t body

reduce (Cnd span () x y z)           = case reduce x of
                                         Lit _ () (Boolean _ False) -> reduce z
                                         Lit _ () (Boolean _ True)  -> reduce y
                                         x'                         -> Cnd span () x' y z

reduce (Let span () x y)
  | not (usesBinder x)               = reduce $ beta (reduce x) y
  | otherwise                        = Let span () (reduce x) (reduce y)

reduce (App span () f a)             = case (reduce f, reduce a) of
                                         (Abs _ () b, a') -> reduce (beta a' b)
                                         (f', a')         -> App span () f' a'

reduce (Abs span () body)            = Abs span () $ reduce body

reduce (Acc span ref x)              = Acc span ref $ reduce x

reduce x                   = x

type BuiltinFunctions = Map Int (Exp Build)
type Scope            = Map Int (Exp Build)

data ConvertError
  = InvalidRecursiveBinding Span
  | MissingParent Int
  | UnboundIndex Int
  deriving Show

type Convert es =
  ( State BuiltinFunctions :> es
  , Error ConvertError :> es
  , Reader Scope :> es
  , State Int :> es
  )

lookupParent
  :: Convert es
  => Span
  -> Scope
  -> Int
  -> Eff es (Exp Build)

lookupParent _ scope i =
  case Map.lookup i scope of
    Just value -> pure value
    Nothing    -> throwError $ MissingParent i

lookupVar :: Convert es => Span -> Int -> Eff es (Exp Build)
lookupVar _ i = do
  scope <- ask @Scope

  case Map.lookup i scope of
    Just x -> pure x
    Nothing -> throwError $ UnboundIndex i

freshId
  :: Convert es
  => Eff es Int

freshId = do
  n <- get @Int
  put @Int (n + 1)
  pure n

usesBinder :: Exp Infer -> Bool
usesBinder = f 0
  where
    f depth (Cnd _ () x y z) = f depth x || f depth y || f depth z
    f depth (Var _ (_, i))   = i == depth
    f depth (Let _ () x y)   = f (depth + 1) x || f (depth + 1) y
    f depth (App _ () x y)   = f depth x || f depth y
    f depth (Abs _ () x)     = f (depth + 1) x
    f _ _                    = False

underLet :: Int -> Span -> Scope -> Scope
underLet localId span scope =
  Map.insert 0 (Exp @Build span (Local localId)) $
    Map.mapKeysMonotonic (+ 1) scope

convertRecAbs
  :: Convert es
  => Span
  -> Exp Infer
  -> Eff es (Exp Build)
convertRecAbs span x = do
  functionId <- freshId
  parentScope <- ask @Scope

  let needed = Set.toAscList (free x)
      capturesNeeded = filter (/= 0) needed

  captures <- traverse (lookupParent span parentScope) capturesNeeded

  let childScope =
        Map.fromList $
          [ (0, Exp @Build span Arg)
          , (1, Exp @Build span (Env 0))
          ]
          ++ [ (sourceIndex + 1, Exp @Build span (Env slot))
             | (sourceIndex, slot) <- zip capturesNeeded [1..]
             ]

  body <- local (const childScope) (convert x)

  modify @BuiltinFunctions $ Map.insert functionId body

  pure $ Exp span $ RecClosure functionId captures

constructorInferToBuild
  :: Constructor Infer
  -> Constructor Build
constructorInferToBuild = \case
  Record span fields ->
    Record span fields

  Single span tys ->
    Single span tys

typInferToBuild
  :: Typ Infer
  -> Typ Build
typInferToBuild = \case
  Named vars constructors ->
    Named vars
      [ (name, constructorInferToBuild ctor)
      | (name, ctor) <- constructors
      ]

freshFunction
  :: Convert es
  => Eff es Int
freshFunction = do
  n <- get @Int
  put @Int (n + 1)
  pure n

lowerConstructor
  :: Convert es
  => Span
  -> TypeId
  -> Int
  -> Int
  -> Eff es (Exp Build)

lowerConstructor span tid tag 0 =
  pure $
    Exp span $
      DataBuild tid tag []

lowerConstructor span tid tag arity = do
  functionId <- freshFunction
  body       <- stage 0

  modify @BuiltinFunctions $
    Map.insert functionId body

  pure $
    Exp span $
      Closure functionId []

  where
    stage i
      | i == arity - 1 =
          pure $
            Exp span $
              DataBuild tid tag $
                previous i ++ [Exp span Arg]

      | otherwise = do
          nextId   <- freshFunction
          nextBody <- stage (i + 1)

          modify @BuiltinFunctions $
            Map.insert nextId nextBody

          pure $
            Exp span $
              Closure nextId $
                previous i ++ [Exp span Arg]

    previous i =
      [ Exp span (Env n)
      | n <- [0 .. i - 1]
      ]

convert :: Convert es => Exp Infer -> Eff es (Exp Build)
convert (Cnd span () x y z) = Cnd span () <$> convert x <*> convert y <*> convert z
convert (App span () f x)   = App span () <$> convert f <*> convert x
convert (Var span (_, i))   = lookupVar span i
convert (Exp s (Free n)) =
  pure $
    Exp s (OutOfScope n)

convert (Acc span binding x) = Acc span (fieldRef binding) <$> convert x
convert (Exp s (Data _ tid tag arity)) =
  lowerConstructor s tid tag arity
convert (Lit s () lit)      = pure $ Lit s () (litInferToBuild lit)

convert (Typ s i typ)       = pure $ Typ s i (typInferToBuild typ)

convert (Let span () rhs body) = do
  localId <- freshId
  parentScope <- ask @Scope

  let letScope = underLet localId span parentScope

  rhs' <-
    if usesBinder rhs
      then case rhs of
        Abs absSpan () x ->
          local (const letScope) (convertRecAbs absSpan x)
        _ ->
          throwError $ InvalidRecursiveBinding span
      else
        local (const letScope) (convert rhs)

  body' <- local (const letScope) (convert body)

  pure $ Let span localId rhs' body'

convert (Abs span () x) = do
  functionId  <- freshId
  parentScope <- ask @Scope

  let needed = Set.toAscList (free x)

  captures <- traverse (lookupParent span parentScope) needed

  let childScope =
        Map.fromList $
          (0, Exp @Build span Arg)
          : [ (sourceIndex + 1, Exp @Build span (Env slot))
            | (sourceIndex, slot) <- zip needed [0..]
            ]

  body <- local (const childScope) (convert x)

  modify @BuiltinFunctions $ Map.insert functionId body

  pure $ Exp span $ Closure functionId captures

runConvert :: Exp Infer -> Either ConvertError (Exp Build, BuiltinFunctions)
runConvert x = convert x & runPureEff
               . runErrorNoCallStack
               . runReader @Scope mempty
               . evalState @Int 0
               . runState @BuiltinFunctions mempty
