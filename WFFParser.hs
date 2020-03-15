{-# LANGUAGE OverloadedStrings #-}

module WFFParser (expressionP, parseWFF) where

import Text.Parsec (Parsec,
    string, spaces, alphaNum, char, (<?>), between, many1, parse, ParseError)
import Control.Applicative ((<|>))
import Data.Text (Text)
import Data.String (fromString)
import Data.Function ((&))

import WFF(WFF(..))

{-
    The grammar used here is
    S -> E B
    E -> ( S ) | U | P
    B -> O E | empty
    U -> N E
    P -> any proposition
    O -> any binary operator
    N -> not symbol
-}

type WFFParser = Parsec Text () (WFF Text)

{-
    Parse a proposition, made of alpha-numeric characters, underscores, and
    apostrophes
-}
propositionP :: WFFParser
propositionP = Prop . fromString <$>
    many1 (alphaNum <|> char '_' <|> char '\'') <?> "proposition"

-- Parse Not symbols
notP :: Parsec Text () (WFF x -> WFF x)
notP = Not <$ (string "-" <|> string "~" <|> string "!" <|> string "¬") <?>
    "negation"

-- Parse Or symbols
orP :: Parsec Text () (WFF x -> WFF x -> WFF x)
orP = (:|:) <$
    (string "\\/" <|> (string "|" <* (string "|" <|> string "")) <|>
        string "+" <|> string ";" <|> string "∨") <?> "disjunction operator"

-- Parse And symbols
andP :: Parsec Text () (WFF x -> WFF x -> WFF x)
andP = (:&:) <$
    (string "/\\" <|> (string "&" <* (string "&" <|> string "")) <|>
        string "*" <|> string "^" <|> string "," <|> string "∧") <?>
    "conjunction operator"

-- Parse Implies symbols
impliesP :: Parsec Text () (WFF x -> WFF x -> WFF x)
impliesP = (:>:) <$
    (string ">" <|> (string "-" *> (string ">" <|> string "->")) <|>
        string "→") <?>
    "implication operator"

-- Parse Equals symbols
equalP :: Parsec Text () (WFF x -> WFF x -> WFF x)
equalP = (:=:) <$
    (("=" <$ many1 (string "=")) <|>
        (string "<" *> (string "->" <|> string "=>")) <|> string "↔") <?>
    "equivalence operator"

-- Parse any unary expression
unaryP :: WFFParser
unaryP = notP <*> (spaces *> safeExpressionP) <?> "unary formula"

-- Parse any binary operator
binOpP :: Parsec Text () (WFF x -> WFF x -> WFF x)
binOpP = orP <|> andP <|> impliesP <|> equalP <?> "binary operator"

-- Parse a binary or other expression
binaryOrExpP :: WFFParser
binaryOrExpP = (&) <$> (safeExpressionP <* spaces) <*> (
    ((fmap flip binOpP <* spaces) <*> safeExpressionP) <|>
    (id <$ string "")
    )

-- Make a parser work inside brackets
bracketted :: Parsec Text () x -> Parsec Text () x
bracketted p = sb '(' ')' <|> sb '[' ']' <|> sb '{' '}' where
    sb o c = between (char o) (char c) $ spaces *> p <* spaces

-- Parse an expression that can be nested in another expression safely
safeExpressionP :: WFFParser
safeExpressionP = bracketted binaryOrExpP <|> unaryP <|> propositionP

-- Parse any expression
expressionP :: WFFParser
expressionP = spaces *> binaryOrExpP <* spaces

-- Given a source and formula in text, parse it
parseWFF :: String -> Text -> Either ParseError (WFF Text)
parseWFF = parse expressionP
