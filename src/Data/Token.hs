module Data.Token where

import Data.Text hiding (show, unwords, replicate, unlines)
import Text.Megaparsec.Char.Lexer hiding (space)
import qualified Data.List.NonEmpty as NE
import Control.Applicative hiding (many)
import qualified Data.Vector as Vector
import qualified Data.Set as Set
import qualified Data.Text as T
import Text.Megaparsec.Stream
import Text.Megaparsec.State
import Data.Vector (Vector)
import Text.Megaparsec.Char
import Text.Megaparsec
import Data.Set (Set)
import Control.Monad
import Data.Bifunctor
import Control.Lens
import Data.Maybe
import Data.Proxy
import Data.Void
import Data.Ast

data Kind
  = Literal (Lit Lexer)
  | LDelim Delim
  | RDelim Delim
  | Keyword Text
  | Ident Text
  | Backslash
  | Question
  | Percent
  | Dollar
  | Colon
  | Space
  | Minus
  | Caret
  | Pound
  | Comma
  | Tilde
  | Grave
  | Slash
  | Star
  | Plus
  | Bang
  | Semi
  | Dot
  | And
  | Eq
  | At
  | Or
  | Lt
  | Gt
  deriving ( Show
           , Ord
           , Eq
           )

data Tok = Tok
  { _span :: Span
  , _kind :: Kind
  }
  deriving ( Show
           , Ord
           , Eq
           )

instance HasSpan Tok where
  getSpan (Tok s _) = s

makePrisms ''Delim
makeLenses ''Delim
makeLenses ''Kind
makePrisms ''Kind
makeLenses ''Tok
makePrisms ''Tok
makeLenses ''Lit
makePrisms ''Lit

type Lex = Parsec Void Text

spanOf :: Ord s => Parsec s Text a -> Parsec s Text (Span, a)
spanOf m = do
      lo <- fromIntegral <$> getOffset
      a <- m
      hi <- fromIntegral <$> getOffset
      pure $ (Span lo hi, a)

tok :: [Text] -> Lex Tok
tok keywords = msum [ w
           , try l
           , k
           , i
           , t
           ]
  where
    w   = uncurry Tok <$> spanOf (Space <$ space1)

    k   = do
      (span, ident) <- spanOf kw
      pure $ Tok span $ Keyword ident
      where
        kw = msum $ string <$> keywords

    i   = do
      (span, ident) <- spanOf it
      pure $ Tok span $ Ident ident
      where
        it = fst <$> match (letterChar >> many (alphaNumChar <|> us))
        us = single '_'

    l   = do
      (span, lit) <- spanOf (msum [ try b, try d', try u, s' ])
      pure $ Tok  span $ Literal lit
      where
        u  = Unsigned () <$> decimal
        d' = Decimal  () <$> signed hspace float
        s' = Signed   () <$> signed hspace decimal
        b  = msum [ t', f ]
          where
            t' = Boolean () True  <$ string "true"
            f  = Boolean () False <$ string "false"

    t   = uncurry Tok <$> spanOf m
      where
        m = flip token Set.empty $ \case
          '('  -> Just $ LDelim Parens
          ')'  -> Just $ RDelim Parens
          '{'  -> Just $ LDelim Braces
          '}'  -> Just $ RDelim Braces
          '['  -> Just $ LDelim Braces
          ']'  -> Just $ RDelim Braces
          '\\' -> Just Backslash
          '?'  -> Just Question
          '%'  -> Just Percent
          '$'  -> Just Dollar
          '^'  -> Just Caret
          ':'  -> Just Colon
          '#'  -> Just Pound
          '-'  -> Just Minus
          '/'  -> Just Slash
          '`'  -> Just Grave
          '~'  -> Just Tilde
          ','  -> Just Comma
          ';'  -> Just Semi
          '!'  -> Just Bang
          '+'  -> Just Plus
          '*'  -> Just Star
          '&'  -> Just And
          '.'  -> Just Dot
          '@'  -> Just At
          '='  -> Just Eq
          '|'  -> Just Or
          '<'  -> Just Lt
          '>'  -> Just Gt
          _    -> Nothing

newtype TokenStream = TokenStream (Vector Tok)
  deriving ( Show
           , Ord
           , Eq
           )

instance Stream TokenStream where
  type Token  TokenStream = Tok
  type Tokens TokenStream = Vector Tok

  tokenToChunk  Proxy = Vector.singleton
  tokensToChunk Proxy = Vector.fromList
  chunkToTokens Proxy = Vector.toList
  chunkLength   Proxy = Vector.length

  take1_ (TokenStream s) = do
    (a, vec) <- Vector.uncons s
    pure $ (a, TokenStream vec)

  takeN_ n (TokenStream s) =
    if Vector.null s && n > 0
    then Nothing
    else Just $ second TokenStream $ Vector.splitAt n s

  takeWhile_ f (TokenStream s) = second TokenStream $ Vector.partition f s

instance VisualStream TokenStream where
  showTokens Proxy = unwords . NE.toList . fmap (show . _kind)

tokenize :: [Text] -> String -> Text -> Either (ParseErrorBundle Text Void) [Tok]
tokenize keywords filename input = runParser (many (tok keywords) <* eof) filename input

data TokenStreamError
  = LexerError (ParseErrorBundle Text Void)
  | ParseError (ParseErrorBundle TokenStream Void)
  deriving Show

parseTokenStream
  :: Parsec Void TokenStream a
  -> [Text]
  -> String
  -> Text
  -> Either TokenStreamError a
parseTokenStream p keywords filename input =
  case tokenize keywords  filename input of
    Left lexErr -> Left (LexerError lexErr)
    Right toks  ->
      let tokVec = Vector.fromList toks
      in case runParser p filename (TokenStream tokVec) of
           Left errBundle -> Left (ParseError errBundle)
           Right a        -> Right a
