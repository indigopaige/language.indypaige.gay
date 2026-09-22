module Data.Ast where

import qualified Data.List.NonEmpty as NE
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text, unpack)
import Text.Megaparsec.Error
import Text.Megaparsec
import Data.Map (Map)
import Control.Lens
import Data.Coerce
import Data.Void
import Data.Set

data Name = Name Text Span
  deriving ( Show
           , Ord
           , Eq
           )

data Span = Span
  { _lo :: Word
  , _hi :: Word
  }
  deriving ( Show
           , Ord
           , Eq
           )

makeLenses ''Span
makePrisms ''Span
makeLenses ''Name
makePrisms ''Name

extend :: Span -> Span -> Span
extend a b = Span (a^.lo) (b^.hi)

class HasSpan a where
  getSpan :: a -> Span

instance HasSpan Name where
  getSpan (Name _ span) = span

type family XUnsigned x
type family XBoolean x
type family XDecimal x
type family XSigned x

data Lit x
  = Signed (XSigned x) Int
  | Boolean (XBoolean x) Bool
  | Decimal (XDecimal x) Double
  | Unsigned (XUnsigned x) Word

litLexerToParse :: Span -> Lit Lexer -> Lit Parse
litLexerToParse span (Unsigned () unsigned) = Unsigned span unsigned
litLexerToParse span (Decimal () decimal)   = Decimal span decimal
litLexerToParse span (Boolean () bool)      = Boolean span bool
litLexerToParse span (Signed () int)        = Signed span int

coerceLit :: Lit Parse -> Lit Infer
coerceLit (Unsigned span unsigned) = Unsigned span unsigned
coerceLit (Decimal span decimal)   = Decimal span decimal
coerceLit (Boolean span bool)      = Boolean span bool
coerceLit (Signed span int)        = Signed span int

litInferToBuild :: Lit Infer -> Lit Build
litInferToBuild (Unsigned span unsigned) = Unsigned span unsigned
litInferToBuild (Decimal span decimal)   = Decimal span decimal
litInferToBuild (Boolean span bool)      = Boolean span bool
litInferToBuild (Signed span int)        = Signed span int

instance HasSpan (Lit Parse) where
  getSpan (Unsigned span _) = span
  getSpan (Decimal span _)  = span
  getSpan (Boolean span _)  = span
  getSpan (Signed span _)   = span

type instance XUnsigned Lexer = ()
type instance XDecimal  Lexer = ()
type instance XBoolean  Lexer = ()
type instance XSigned   Lexer = ()

type instance XUnsigned Parse = Span
type instance XDecimal  Parse = Span
type instance XBoolean  Parse = Span
type instance XSigned   Parse = Span

type instance XUnsigned Infer = Span
type instance XDecimal  Infer = Span
type instance XBoolean  Infer = Span
type instance XSigned   Infer = Span

type instance XUnsigned Build = Span
type instance XDecimal  Build = Span
type instance XBoolean  Build = Span
type instance XSigned   Build = Span

deriving instance Show (Lit Lexer)
deriving instance Show (Lit Parse)
deriving instance Show (Lit Infer)
deriving instance Show (Lit Build)

deriving instance Ord (Lit Lexer)
deriving instance Ord (Lit Parse)
deriving instance Ord (Lit Infer)
deriving instance Ord (Lit Build)

deriving instance Eq (Lit Lexer)
deriving instance Eq (Lit Parse)
deriving instance Eq (Lit Infer)
deriving instance Eq (Lit Build)

-- Phases
data Lexer
data Parse
data Infer
data Build

type family XApp x
type family XAbs x
type family XExp x
type family XVar x
type family XCnd x
type family XLet x
type family XLit x

data Exp x
  = Cnd Span (XCnd x) (Exp x) (Exp x) (Exp x)
  | Let Span (XLet x) (Exp x) (Exp x)
  | App Span (XApp x) (Exp x) (Exp x)
  | Lit Span (XLit x) (Lit x)
  | Abs Span (XAbs x) (Exp x)
  | Var Span (XVar x)
  | Exp Span (XExp x)

instance Plated (Exp x) where 
  plate f (Cnd s e x y z) = Cnd s e <$> f x <*> f y <*> f z
  plate f (Let s e l r)   = Let s e <$> f l <*> f r
  plate f (App s e l r)   = App s e <$> f l <*> f r
  plate f (Abs s e e')    = Abs s e <$> f e'
  plate _ x               = pure x

instance HasSpan (Exp Parse) where
  getSpan (Cnd span _ _ _ _) = span
  getSpan (Let span _ _ _)   = span
  getSpan (App span _ _ _)   = span
  getSpan (Lit span _ _)     = span
  getSpan (Abs span _ _)     = span
  getSpan (Var span _)       = span
  getSpan (Exp _ v)          = absurd v

type instance XApp Parse = ()
type instance XApp Infer = ()
type instance XApp Build = ()

type instance XAbs Parse = Name
type instance XAbs Infer = ()
type instance XAbs Build = ()

type instance XVar Parse = Name
type instance XVar Infer = (Name, Int)
type instance XVar Build = (Name, Int)

type instance XLet Parse = Name
type instance XLet Infer = ()
type instance XLet Build = ()

type instance XCnd Parse = ()
type instance XCnd Infer = ()
type instance XCnd Build = ()

type instance XLit Parse = ()
type instance XLit Infer = ()
type instance XLit Build = ()

type instance XExp Parse = Void
type instance XExp Infer = Name
type instance XExp Build = XBuild

deriving instance Show (Exp Parse)
deriving instance Show (Exp Infer)
deriving instance Show (Exp Build)

deriving instance Ord  (Exp Parse)
deriving instance Ord  (Exp Infer)
deriving instance Ord  (Exp Build)

deriving instance Eq   (Exp Parse)
deriving instance Eq   (Exp Infer)
deriving instance Eq   (Exp Build)

data Delim
  = Parens
  | Braces
  | Square
  deriving ( Show
           , Ord
           , Eq
           )

keywords :: [Text]
keywords = [ "else"
           , "then"
           , "let"
           , "if"
           , "in"
           ]

data Ty
  = TyCon Text [Ty]
  | TyVar Text
  deriving ( Show
           , Ord
           , Eq
           )

instance Plated Ty where
  plate f (TyCon s x) = TyCon s <$> traverse f x
  plate _ x           = pure x

infixr 9 :->

pattern a :-> b = TyCon "->" [a, b]
pattern F s     = TyCon s []
pattern TyWrd   = F "wrd"
pattern TyNum   = F "num"
pattern TyBin   = F "bin"
pattern TyDec   = F "dec"

data Constraint  = Constraint Ty Ty
data Scheme      = Forall (Set Text) Ty

dec :: [Text]
dec = [ "addDec"
      , "subDec"
      , "mulDec"
      , "divDec"
      ]

wrd :: [Text]
wrd = [ "addWrd"
      , "subWrd"
      , "mulWrd"
      , "divWrd"
      ]

num :: [Text]
num = [ "addNum"
      , "subNum"
      , "mulNum"
      , "divNum"
      ]

opType :: Text -> Maybe Ty
opType name
  | name `elem` dec = Just TyDec
  | name `elem` wrd = Just TyWrd
  | name `elem` num = Just TyNum
  | otherwise        = Nothing

builtins :: Map Text Scheme
builtins = Map.fromList (eq ++ oper)
  where
    eq   = [ ("eq", Forall (Set.singleton "a") (TyVar "a" :-> TyVar "a" :-> TyBin)) ]
    mono = Forall mempty
    oper = concat [dec', wrd', num']
      where
        dec' = (,mono d3) <$> dec
        wrd' = (,mono w3) <$> wrd
        num' = (,mono i3) <$> num

        i3   = TyNum :-> TyNum :-> TyNum
        w3   = TyWrd :-> TyWrd :-> TyWrd
        d3   = TyDec :-> TyDec :-> TyDec

data XBuild
  = Closure Int [Exp Build]
  | OutOfScope Name
  | Env Int
  | Arg
  deriving ( Show
           , Ord
           , Eq
           )

free :: Exp Infer -> Set Int
free = f 1
  where
    f n (Var _ (_, n')) | n' >= n = Set.singleton (n' - n)
    f _ (Var _ _)                 = mempty

    f n (Abs _ () x)              = f (n + 1) x

    f n (App _ () x y)            = f n x `Set.union` f n y

    f _ _                         = mempty

