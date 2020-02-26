{-# LANGUAGE OverloadedStrings #-}

module WFFParser (expressionP, parseWFF) where

import Text.Parsec (Parsec,
    string, spaces, alphaNum, char, (<?>), between, many1, parse, ParseError)
import Control.Applicative ((<|>))
import Data.Text (Text)
import Data.String (fromString)
import Data.Function ((&))

import WFF(WFF(..))

type WFFParser = Parsec Text () (WFF Text)

propositionP :: WFFParser
propositionP = Prop . fromString <$>
    many1 (alphaNum <|> char '_' <|> char '\'') <?> "proposition"

notP :: Parsec Text () (WFF x -> WFF x)
notP = Not <$ (string "-" <|> string "~" <|> string "!" <|> string "¬") <?>
    "negation"

orP :: Parsec Text () (WFF x -> WFF x -> WFF x)
orP = (:|:) <$
    (string "\\/" <|> (string "|" <* (string "" <* string "|")) <|>
        string "+" <|> string ";" <|> string "∨") <?> "disjunction operator"

andP :: Parsec Text () (WFF x -> WFF x -> WFF x)
andP = (:&:) <$
    (string "/\\" <|> (string "&" <* (string "" <* string "&")) <|>
        string "*" <|> string "^" <|> string "," <|> string "∧") <?>
    "conjunction operator"

impliesP :: Parsec Text () (WFF x -> WFF x -> WFF x)
impliesP = (:>:) <$
    (string ">" <|> (string "-" *> (string ">" <|> string "->")) <|>
        string "→") <?>
    "implication operator"

equalP :: Parsec Text () (WFF x -> WFF x -> WFF x)
equalP = (:=:) <$
    (("=" <$ many1 (string "=")) <|>
        (string "<" *> (string "->" <|> string "=>")) <|> string "↔") <?>
    "equivalence operator"

unaryP :: WFFParser
unaryP = notP <*> (spaces *> safeExpressionP) <?> "unary formula"

binOpP :: Parsec Text () (WFF x -> WFF x -> WFF x)
binOpP = orP <|> andP <|> impliesP <|> equalP <?> "binary operator"

binaryOrExpP :: WFFParser
binaryOrExpP = (&) <$> safeExpressionP <*> (
    ((spaces *> fmap flip binOpP <* spaces) <*> safeExpressionP) <|>
    (id <$ string "")
    )

bracketted :: Parsec Text () x -> Parsec Text () x
bracketted p = sb '(' ')' <|> sb '[' ']' <|> sb '{' '}' where
    sb o c = between (char o) (char c) $ spaces *> p <* spaces

safeExpressionP :: WFFParser
safeExpressionP = bracketted binaryOrExpP <|> unaryP <|> propositionP

expressionP :: WFFParser
expressionP = spaces *> binaryOrExpP <* spaces

-- Given a source and formula in text, parse it
parseWFF :: String -> Text -> Either ParseError (WFF Text)
parseWFF = parse expressionP
