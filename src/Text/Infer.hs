module Text.Infer where

import Control.Lens hiding (Context, (.>))
import Effectful.Writer.Static.Local
import Effectful.State.Static.Local
import qualified Data.Set as Set
import qualified Data.Map as Map
import Effectful.Reader.Static
import Effectful.Error.Static
import Data.Text (Text, pack)
import Data.Map (Map)
import Data.Set (Set)
import Data.List
import Effectful
import Data.Ast

expParseToInfer :: Exp Parse -> Exp Infer
expParseToInfer e = f e & runPureEff . runReader @[Text] []
  where
    f (Cnd span () x y z)          = Cnd span () <$> f x <*> f y <*> f z
    f (App span () x y)            = App span () <$> f x <*> f y

    f (Let span (Name name _) x y) = do
      lhs <- f x
      rhs <- local (name:) (f y)
      pure $ Let span () lhs rhs

    f (Abs span (Name name _) x)   = do
      lhs <- local (name:) (f x)
      pure $ Abs span () lhs

    f (Lit span () lit)   = pure $ Lit span () (coerceLit lit)

    f (Var span n@(Name name _))   = g . elemIndex name <$> ask
      where
        g (Just x) = Var span (n, (fromIntegral x))
        g Nothing  = Exp span n


type Constraints = [Constraint]
type Context     = [Scheme]

type Count       = Int

data Env         = Env (Map Text (Exp Infer)) (Map Text Ty)

type Subst       = Map Text Ty

type Builtins    = Map Text Scheme

data InferError
  = Infinite Text Ty
  | Mismatch Ty Ty
  | Undefined Name
  | Unbound Name
  deriving Show

type Inf es =
  ( Writer Constraints :> es
  , Error InferError :> es
  , Reader Builtins :> es
  , Reader Context :> es
  , State Count :> es
  )

infixr 8 <=>

(<=>) :: Inf es => Ty -> Ty -> Eff es ()
(<=>) x y = tell (Constraint x y :[])

fresh :: Inf es => Eff es Ty
fresh = do
  count <- get @Count
  modify @Count (+1)
  pure . TyVar . pack $ show count

(.>) :: Subst -> Subst -> Subst
(.>) a b = (a .$) <$> (b `Map.union` a)

class Substitutable a where
  (.$) :: Subst -> a -> a
  vars :: a -> Set Text

instance Substitutable Ty where
  vars (TyVar t)      = Set.singleton t
  vars (TyCon _ ts)   = foldr (Set.union . vars) mempty ts

  (.$) s t@(TyVar t') = Map.findWithDefault t t' s
  (.$) s x            = x & plate %~ (s .$)

instance Substitutable Scheme where
  vars (Forall v t)   = vars t `Set.difference` v
  (.$) s (Forall v t) = Forall v $ foldr Map.delete s v .$ t

instance Substitutable Constraint where
  vars (Constraint t t')   = vars t `Set.union` vars t'
  (.$) s (Constraint t t') = Constraint (s .$ t) (s .$ t')

instance Substitutable a => Substitutable [a] where
  vars = foldr (Set.union . vars) mempty
  (.$) = fmap . (.$)

instantiate :: Inf es => Scheme -> Eff es Ty
instantiate (Forall v t) = do
  let vars = Set.toList v
  vs <- traverse (const fresh) vars
  let subs = Map.fromList (zip vars vs)
  pure $ subs .$ t

generalize :: Context -> Ty -> Scheme
generalize ctx t = Forall (vars t `Set.difference` vars ctx) t

infer :: Inf es => Exp Infer -> Eff es Ty
infer = \case
  Lit _ () (Unsigned _ _) -> pure $ TyWrd
  Lit _ () (Boolean _ _)  -> pure $ TyBin
  Lit _ () (Decimal _ _)  -> pure $ TyDec
  Lit _ () (Signed _ _)   -> pure $ TyNum

  Let span () x y -> do
    (et, cs) <- listen (infer x)
    subst    <- runSolve cs
    let et'  = subst .$ et
    ctx      <- ask
    let ctx' = subst .$ ctx
    let es   = generalize ctx' et'
    local (const (es : ctx')) (infer y)

  Cnd _ () x y z -> do
    xt <- infer x
    yt <- infer y
    zt <- infer z

    xt <=> TyBin
    yt <=> zt

    pure yt

  App _ () f a -> do
    ft <- infer f
    at <- infer a
    rt <- fresh

    ft <=> at :-> rt

    pure rt

  Abs _ _ e -> do
    pt <- fresh
    let ps = Forall mempty pt
    et <- local (ps :) (infer e)
    pure $ pt :-> et

  Var _ (n, v) -> do
    ctx <- ask @Context
    case drop v ctx of
      (t:_) -> instantiate t
      []    -> throwError (Undefined n)

  Exp _ n@(Name x _) -> do
    m <- ask @Builtins
    case Map.lookup x m of

      Just x  -> instantiate x
      Nothing -> throwError $ Unbound n

bind :: Error InferError :> es => Text -> Ty -> Eff es Subst
bind v t
  | v `Set.member` vars t = throwError $ Infinite v t
  | otherwise             = pure $ Map.singleton v t
 
unify :: Error InferError :> es => Ty -> Ty -> Eff es Subst
unify a b | a == b = pure mempty
unify (TyVar v) t  = bind v t
unify t (TyVar v)  = bind v t

unify a@(TyCon n ts) b@(TyCon n' ts')
  | n /= n'   = throwError $ Mismatch a b
  | otherwise = unifyMany ts ts'
  where
    unifyMany [] []               = pure mempty
    unifyMany (t : ts) (t' : ts') = do
      s  <- unify t t'
      s' <- unifyMany (s .$ ts) (s .$ ts')
      pure $ s' .> s

solve :: Error InferError :> es => Subst -> [Constraint] -> Eff es Subst
solve s []                       = pure s
solve s ((Constraint t t') : cs) = do
  s' <- unify t t'
  solve (s' .> s) (s' .$ cs)

runSolve :: Error InferError :> es => [Constraint] -> Eff es Subst
runSolve = solve mempty

runInfer :: Error InferError :> es => Exp Infer -> Eff es (Ty, Constraints)
runInfer i = infer i & evalState @Count 0
             . runReader @Builtins builtins
             . runReader @Context mempty
             . runWriter @Constraints

inferTy :: Exp Infer -> Either InferError Ty
inferTy e = runPureEff $ runErrorNoCallStack $ do
  (t, cs) <- runInfer e
  s       <- runSolve cs
  pure $ s .$ t
