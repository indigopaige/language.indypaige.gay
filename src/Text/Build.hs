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
shift d c (Let span () x y) = Let span () (shift d c x) $ shift d (c + 1) y

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
        g (Let span () x y) = Let span () (f d x) (f (d + 1) y)

        g (Abs span () x)   = Abs span () (f (d + 1) x)
        
        g lam@(Var span (_, k))
          | k == j + d = shift d 0 s
          | otherwise  = lam

        g x                 = x & plate %~ g

beta :: Exp Infer -> Exp Infer -> Exp Infer
beta x y = shift (-1) 0 $ subst 0 (shift 1 0 x) y

reduce :: Exp Infer -> Exp Infer
reduce (Cnd span () x y z) = case reduce x of
                             Lit _ () (Boolean _ True) -> reduce y
                             Lit _ () (Boolean _ False) -> reduce z
                             x'                        -> Cnd span () x' y z

reduce (Let span () x y)   = reduce $ beta (reduce x) y

reduce (App span () f a)   = case (reduce f, reduce a) of
                             (Abs _ () b, a') -> reduce (beta a' b)
                             (f', a')         -> App span () f a'

reduce x                   = x

type BuiltinFunctions = Map Int (Exp Build)
type Scope            = Map Int (Exp Build)

data ConvertError
  = MissingParent Int
  | LetSurvival Span
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

lookupParent span _ 0  = pure $ Exp span Arg
lookupParent _ scope i =
  case Map.lookup (i - 1) scope of
    Just value -> pure value
    Nothing    -> throwError $ MissingParent i

lookupVar :: Convert es => Span -> Int -> Eff es (Exp Build)
lookupVar span 0 = pure $ Exp span Arg
lookupVar span i = do
  scope <- ask @Scope

  case Map.lookup (i - 1) scope of
    Just x -> pure x
    _      -> throwError $ UnboundIndex i

freshFunction
  :: Convert es
  => Eff es Int

freshFunction = do
  n <- get @Int

  put @Int (n + 1)

  pure n

convert :: Convert es => Exp Infer -> Eff es (Exp Build)
convert (Cnd span () x y z) = Cnd span () <$> convert x <*> convert y <*> convert z
convert (App span () f x)   = App span () <$> convert f <*> convert x
convert (Var span (_, i))   = lookupVar span i
convert (Exp s n)           = pure $ Exp s (OutOfScope n)
convert (Let s () _ _)      = throwError $ LetSurvival s
convert (Lit s () lit)      = pure $ Lit s () (litInferToBuild lit)
convert (Abs span () x)     = do
  functionId  <- freshFunction
  parentScope <- ask @Scope

  let needed = Set.toAscList (free x)

  captures    <- traverse (lookupParent span parentScope) needed

  let childScope = Map.fromList [ (sourceIndex, Exp @Build span (Env slot))
                                | (sourceIndex, slot) <- zip needed [0..]
                                ]

  body        <- local (const childScope) (convert x)

  modify @BuiltinFunctions $ Map.insert functionId body

  pure $ Exp span $ Closure functionId captures

runConvert :: Exp Infer -> Either ConvertError (Exp Build, BuiltinFunctions)
runConvert x = convert x & runPureEff
               . runErrorNoCallStack
               . runReader @Scope mempty
               . evalState @Int 0
               . runState @BuiltinFunctions mempty
