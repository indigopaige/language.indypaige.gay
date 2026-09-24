module Text.Parse where

import qualified Data.List.NonEmpty as NE
import qualified Data.Set as Set
import Data.Text (Text, unpack)
import Prelude hiding (span)
import Text.Megaparsec
import Control.Monad
import Control.Lens
import Data.Token
import Data.Void
import Data.Ast

type Parser = Parsec Void TokenStream

kind' :: Kind -> Parser ()
kind' = void . aKind

aKind :: Kind -> Parser Tok
aKind k = satisfy ((== k) . (^.kind))

lexeme :: Kind -> Parser ()
lexeme k = space *> kind' k <* space

parens, braces, square :: Parser a -> Parser a
parens m = kind' (LDelim Parens) *> m <* kind' (RDelim Parens)
braces m = kind' (LDelim Braces) *> m <* kind' (RDelim Braces)
square m = kind' (LDelim Square) *> m <* kind' (RDelim Square)

space :: Parser ()
space = kind' Space <|> pure ()

space1 :: Parser ()
space1 = kind' Space

text :: Text -> Parser Name
text txt = token f mempty <?> (unpack txt)
  where
    f (Tok span (Ident ident))
      | ident == txt = Just (Name ident span)
      | otherwise    = Nothing
    f _              = Nothing

kw :: Text -> Parser Name
kw k = token f keywords'  <?> "keyword"
  where
    keywords' = Set.fromList (f <$> keywords)
      where
        f txt = Label $ NE.fromList (unpack txt)

    f (Tok span (Keyword kw))
      | kw == k   = Just (Name kw span)
      | otherwise = Nothing
    f _           = Nothing

name :: Parser Name
name = token f mempty <?> "name"
  where
    f (Tok span (Ident ident)) = Just (Name ident span)
    f _                        = Nothing

lit :: Parser (Lit Parse)
lit = token f mempty
  where
    f (Tok span (Literal lit)) = Just (litLexerToParse span lit)
    f _                        = Nothing

expr :: Parser (Exp Parse)
expr = msum [ lit'
            , cnd
            , let'
            , typ
            , try abs
            , try app
            , post
            ]
  where
    atom = msum [ lit'
                , typ
                , parens expr
                , var
                ]

    post = do
      x <- atom
      f <- many $ try $ kind' Dot *> name

      pure $ foldl project x f
      where
        project x field = Acc
          (extend (getSpan x) (getSpan field))
          field
          x

    lit' = lit <&> \x ->
      Lit (getSpan x) () x

    var  = name <&> \n@(Name text s) ->
      Var s (Name text s)

    let' = do
      letName <- kw "let"
      space
      binding <- name
      space
      kind' Eq
      space
      binded  <- expr
      space
      kw "in"
      space
      follow  <- expr

      let span = extend
            (getSpan letName)
            (getSpan follow)

      pure $ Let span binding binded follow

    cnd  = do
      ifName <- kw "if"
      space
      cond   <- expr
      space
      kw "then"
      space
      succ   <- expr
      space
      kw "else"
      space
      fail   <- expr

      let span = extend
            (getSpan ifName)
            (getSpan fail)

      pure $ Cnd span () cond succ fail

    abs  = do
      n <- name
      space
      kind' Colon
      space
      x <- expr

      let span = extend
            (getSpan n)
            (getSpan x)

      pure $ Abs span n x

    app  = do
      f <- post
      x <- some $ try (space1 >> post)
      pure $ foldl g f x
      where
        g f x = App (extend (getSpan f)
                            (getSpan x)) () f x

    typ = do
      typeName <- kw "type"
      space
      tys <- name `sepBy` space
      space
      colon <- aKind Colon
      space
      vrs <- variant `sepBy` try (lexeme Or)

      let r = case vrs of
                   [] -> getSpan colon
                   xs -> getSpan (last $ snd <$> xs)
          s = extend (getSpan typeName) r

      pure $ Typ s () (Named tys vrs)
        where
          variant = do
            v <- name
            let span = getSpan v
            c <- try (record span) <|> single span
            pure (v, c)

          single span = do
            xs <- many (try (space1 *> ty))
            case xs of              
              [] -> pure $ Single span []
              xs -> let span' = extend span (getSpan $ last xs)
                    in pure $ Single span' xs

          record span = do
            space
            r <- braces $ (`sepBy1` kind' Comma) $ do
              space
              recordName <- name
              space
              kind' Colon
              space
              recordType <- ty
              space
              pure (recordName, recordType)

            let span = extend
                  (getSpan . fst $ let (x:_) = r in x)
                  (getSpan . snd $ last r)

            pure $ Record span r

    ty     = arr
      where
        val = TyVar <$> name
        arr = do
          lhs <- val <|> (parens ty)

          option lhs $ try $ do
            space
            kind' Minus
            kind' Gt
            space
            rhs <- ty

            pure $ lhs :-> rhs
