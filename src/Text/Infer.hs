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

data ConstructorRef =
  ConstructorRef TypeId Int Int
  deriving (Show, Ord, Eq)

type ConstructorScope =
  Map Text ConstructorRef

constructorSchemes
  :: TypeId
  -> Typ Infer
  -> Builtins

constructorSchemes tid (Named params constructors) =
  Map.fromList $
    make <$> constructors

  where
    bound =
      Set.fromList
        [ name
        | Name name _ <- params
        ]

    result =
      TyNom tid $
        TyVar <$> params

    make (Name name _, constructor) =
      ( name
      , Forall bound $
          constructorTy constructor
      )

    constructorTy = \case
      Single _ tys ->
        foldr (:->) result tys

      Record _ fields ->
        foldr (:->) result $
          snd <$> fields

data TypeBinding = TypeBinding
  { typeBindingId    :: TypeId
  , typeBindingArity :: Int
  }
  deriving (Show, Ord, Eq)

type TypeScope = Map Text TypeBinding
type TypeDefs  = Map TypeId (Typ Infer)

data TypeState = TypeState
  { nextTypeId :: Int
  , typeDefs   :: TypeDefs
  }
  deriving Show

emptyTypeState :: TypeState
emptyTypeState = TypeState
  { nextTypeId = 0
  , typeDefs   = mempty
  }

type Prep es =
  ( Reader [Text] :> es
  , Reader TypeScope :> es
  , State TypeState :> es
  , Error InferError :> es
  , Reader ConstructorScope :> es
  , Reader FieldScope :> es
  )

constructorArity :: Constructor x -> Int
constructorArity = \case
  Single _ tys ->
    length tys

  Record _ fields ->
    length fields

constructorScope
  :: TypeId
  -> Typ Infer
  -> ConstructorScope

constructorScope tid (Named _ constructors) =
  Map.fromList
    [ (name, ConstructorRef tid tag (constructorArity constructor))
    | (tag, (Name name _, constructor)) <-
        zip [0..] constructors
    ]

expParseToInfer
  :: Exp Parse
  -> Either InferError (Exp Infer, TypeDefs)
expParseToInfer e =
  f e
    & runReader @[Text] []
    & runReader @ConstructorScope mempty
    & runReader @FieldScope mempty
    & runReader @TypeScope mempty
    & runState @TypeState emptyTypeState
    & runErrorNoCallStack
    & runPureEff
    & fmap (\(e', st) -> (e', typeDefs st))
  where
    f = \case
      Cnd span () x y z -> Cnd span () <$> f x <*> f y <*> f z
      App span () x y -> App span () <$> f x <*> f y

      Acc span field@(Name name _) x -> do
        fields <- ask @FieldScope

        binding <- case Map.lookup name fields of
                     Just binding -> pure binding
                     Nothing -> throwError $ UnknownField field
        x' <- f x

        pure $ Acc span binding x'

      Lit span () lit -> pure $ Lit span () (coerceLit lit)

      Abs span (Name name _) body -> do
        body' <- local @[Text] (name :) (f body)
        pure $ Abs span () body'

      Var span n@(Name name _) -> do
        terms <- ask @[Text]

        case elemIndex name terms of
          Just i -> pure $ Var span (n, fromIntegral i)

          Nothing -> do
            constructors <- ask @ConstructorScope

            pure $ case Map.lookup name constructors of
              Just (ConstructorRef tid tag arity) -> Exp span $ Data n tid tag arity
              Nothing -> Exp span $ Free n

      Let span (Name name _) (Typ typeSpan () def) body -> do
        tid <- freshTypeId

        let binding = TypeBinding
              { typeBindingId    = tid
              , typeBindingArity = length (typParams def)
              }

        def' <- local @TypeScope
                (Map.insert name binding)
                (resolveTyp def)

        registerType tid def'

        let constructors = constructorScope tid def'
            fields       = fieldScope tid def'

        body' <- local @[Text] (name :)
                 $ local @TypeScope (Map.insert name binding)
                 $ local @ConstructorScope (constructors `Map.union`)
                 $ local @FieldScope (fields `Map.union`)
                 $ f body

        pure $ Let span () (Typ typeSpan tid def') body'
  
      Let span (Name name _) x y -> do
        l <- f x

        r <- local @[Text] (name :) (f y)

        pure $ Let span () l r

      Typ span () def -> do
        tid  <- freshTypeId
        def' <- resolveTyp def

        registerType tid def'

        pure $ Typ span tid def'

freshTypeId :: State TypeState :> es => Eff es TypeId
freshTypeId = do
  st <- get @TypeState
  let tid = TypeId (nextTypeId st)
  put @TypeState st { nextTypeId = nextTypeId st + 1 }
  pure tid

registerType
  :: State TypeState :> es
  => TypeId
  -> Typ Infer
  -> Eff es ()
registerType tid def =
  modify @TypeState $ \st ->
    st { typeDefs = Map.insert tid def (typeDefs st) }

fieldScope
  :: TypeId
  -> Typ Infer
  -> FieldScope

fieldScope tid (Named params [(_, Record _ fields)]) =
  Map.fromList
    [ (name, binding ty index)
    | (index, (Name name _, ty)) <-
        zip [0..] fields
    ]

  where
    bound =
      Set.fromList
        [ name
        | Name name _ <- params
        ]

    recordTy =
      TyNom tid $
        TyVar <$> params

    binding ty index =
      FieldBinding
        { fieldRef =
            FieldRef
              { fieldTypeId = tid
              , fieldTag    = 0
              , fieldIndex  = index
              }

        , fieldScheme =
            Forall bound $
              recordTy :-> ty
        }

fieldScope _ _ =
  mempty

typParams :: Typ x -> [Name]
typParams (Named params _) = params

nameText :: Name -> Text
nameText (Name name _) = name

firstDuplicate :: [Name] -> Maybe Name
firstDuplicate = go mempty
  where
    go _ [] = Nothing
    go seen (n : ns)
      | nameText n `Set.member` seen = Just n
      | otherwise = go (Set.insert (nameText n) seen) ns

checkParams
  :: Error InferError :> es
  => [Name]
  -> Eff es ()
checkParams params =
  case firstDuplicate params of
    Just n  -> throwError $ DuplicateTypeVariable n
    Nothing -> pure ()

builtinType :: Text -> Maybe Ty
builtinType = \case
  "wrd"  -> Just TyWrd
  "num"  -> Just TyNum
  "bin"  -> Just TyBin
  "dec"  -> Just TyDec
  "type" -> Just $ TyCon "type" []
  _      -> Nothing

resolveTyp
  :: Prep es
  => Typ Parse
  -> Eff es (Typ Infer)
resolveTyp (Named params constructors) = do
  checkParams params

  case firstDuplicate (fst <$> constructors) of
    Just n  -> throwError $ DuplicateConstructor n
    Nothing -> pure ()

  let params' = Set.fromList $ nameText <$> params

  constructors' <- traverse
    (\(name, constructor) ->
      (name,) <$> resolveConstructor params' constructor)
    constructors

  pure $ Named params constructors'

resolveConstructor
  :: Prep es
  => Set Text
  -> Constructor Parse
  -> Eff es (Constructor Infer)
resolveConstructor params = \case
  Single span tys ->
    Single span <$> traverse (resolveTy params) tys

  Record span fields -> do
    case firstDuplicate (fst <$> fields) of
      Just n  -> throwError $ DuplicateField n
      Nothing -> pure ()

    fields' <- traverse
      (\(name, ty) -> (name,) <$> resolveTy params ty)
      fields

    pure $ Record span fields'

resolveTy
  :: Prep es
  => Set Text
  -> Ty
  -> Eff es Ty
resolveTy params = \case
  TyVar n@(Name name _)
    | name `Set.member` params ->
        pure $ TyVar n

    | Just ty <- builtinType name ->
        pure ty

    | otherwise -> do
        scope <- ask @TypeScope
        case Map.lookup name scope of
          Nothing ->
            throwError $ UnboundTypeVariable n

          Just (TypeBinding tid 0) ->
            pure $ TyNom tid []

          Just (TypeBinding _ expected) ->
            throwError $ WrongTypeArity name expected 0

  TyCon "->" [lhs, rhs] ->
    (:->) <$> resolveTy params lhs <*> resolveTy params rhs

  TyCon name args -> do
    args' <- traverse (resolveTy params) args

    case builtinType name of
      Just ty
        | null args -> pure ty

      _ -> do
        scope <- ask @TypeScope
        case Map.lookup name scope of
          Nothing ->
            throwError $ UnboundTypeConstructor name

          Just (TypeBinding tid expected)
            | expected == length args' ->
                pure $ TyNom tid args'

            | otherwise ->
                throwError $ WrongTypeArity name expected (length args')

  TyNom tid args ->
    TyNom tid <$> traverse (resolveTy params) args

type Constraints = [Constraint]
type Context     = [Scheme]

type Count       = Int

data Env         = Env (Map Text (Exp Infer)) (Map Text Ty)

type Subst       = Map Text Ty

type Builtins    = Map Text Scheme

type FieldScope  = Map Text FieldBinding

data InferError
  = Infinite Text Ty
  | Mismatch Ty Ty
  | Undefined Name
  | Unbound Name
  | UnboundTypeVariable Name
  | UnboundTypeConstructor Text
  | WrongTypeArity Text Int Int
  | DuplicateTypeVariable Name
  | DuplicateConstructor Name
  | UnknownField Name
  | DuplicateField Name
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
  pure $ TyVar $ Name (pack $ show count) dummy

(.>) :: Subst -> Subst -> Subst
(.>) a b = (a .$) <$> (b `Map.union` a)

class Substitutable a where
  (.$) :: Subst -> a -> a
  vars :: a -> Set Text

instance Substitutable Ty where
  vars (TyVar (Name name _)) = Set.singleton name
  vars (TyCon _ ts)          = vars ts
  vars (TyNom _ ts)          = vars ts

  (.$) s t@(TyVar (Name name _)) = Map.findWithDefault t name s
  (.$) s (TyCon name ts)          = TyCon name (s .$ ts)
  (.$) s (TyNom tid ts)           = TyNom tid (s .$ ts)

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
  let names = Set.toList v
  vs <- traverse (const fresh) names
  let subs = Map.fromList (zip names vs)
  pure $ subs .$ t

generalize :: Context -> Ty -> Scheme
generalize ctx t = Forall (vars t `Set.difference` vars ctx) t

inferFree
  :: Inf es
  => Name
  -> Eff es Ty

inferFree n@(Name x _) = do
  m <- ask @Builtins

  case Map.lookup x m of
    Just scheme ->
      instantiate scheme

    Nothing ->
      throwError $
        Unbound n

infer :: Inf es => Exp Infer -> Eff es Ty
infer = \case
  Lit _ () (Unsigned _ _) -> pure TyWrd
  Lit _ () (Boolean _ _)  -> pure TyBin
  Lit _ () (Decimal _ _)  -> pure TyDec
  Lit _ () (Signed _ _)   -> pure TyNum

  Acc _ binding x -> do
    xt <- infer x

    selectorTy <- instantiate $ fieldScheme binding

    resultTy <- fresh

    selectorTy <=> (xt :-> resultTy)

    pure resultTy

  Let _ () (Typ _ tid def) body -> do
    let constructors =
          constructorSchemes tid def

        typeScheme =
          Forall mempty TyTyp

    local @Context
      (typeScheme :)
      $ local @Builtins
          (constructors `Map.union`)
      $ infer body

  Typ _ _ _ ->
    pure $ TyCon "type" []

  Let _ () x y -> do
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
      (t : _) -> instantiate t
      []      -> throwError $ Undefined n

  Exp _ (Free n) ->
    inferFree n

  Exp _ (Data n _ _ _) ->
    inferFree n

bind :: Error InferError :> es => Text -> Ty -> Eff es Subst
bind v (TyVar (Name v' _))
  | v == v' = pure mempty
bind v t
  | v `Set.member` vars t = throwError $ Infinite v t
  | otherwise             = pure $ Map.singleton v t

unify :: Error InferError :> es => Ty -> Ty -> Eff es Subst
unify (TyVar (Name v _)) t = bind v t
unify t (TyVar (Name v _)) = bind v t

unify a@(TyCon n ts) b@(TyCon n' ts')
  | n /= n'                  = throwError $ Mismatch a b
  | length ts /= length ts'  = throwError $ Mismatch a b
  | otherwise                = unifyMany ts ts'

unify a@(TyNom i ts) b@(TyNom i' ts')
  | i /= i'                  = throwError $ Mismatch a b
  | length ts /= length ts'  = throwError $ Mismatch a b
  | otherwise                = unifyMany ts ts'

unify a b = throwError $ Mismatch a b

unifyMany
  :: Error InferError :> es
  => [Ty]
  -> [Ty]
  -> Eff es Subst
unifyMany [] [] = pure mempty
unifyMany (t : ts) (t' : ts') = do
  s  <- unify t t'
  s' <- unifyMany (s .$ ts) (s .$ ts')
  pure $ s' .> s
unifyMany _ _ = error "unifyMany: mismatched list lengths"

solve :: Error InferError :> es => Subst -> [Constraint] -> Eff es Subst
solve s [] = pure s
solve s (Constraint t t' : cs) = do
  s' <- unify (s .$ t) (s .$ t')
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
