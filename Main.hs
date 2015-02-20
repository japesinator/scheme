module Main where

import Control.Monad
import System.Environment
import Text.ParserCombinators.Parsec hiding (spaces)

-- Parsing
-- {{{

symbol :: Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

spaces :: Parser ()
spaces = skipMany1 space

escapedChars :: Parser Char
escapedChars = do
                 char '\\'
                 x <- oneOf "\\\"nrt"
                 return $ case x of
                               'n' -> '\n'
                               'r' -> '\r'
                               't' -> '\t'
                               _   -> x

parseString :: Parser LispVal
parseString = do
                char '"'
                x <- many $ escapedChars <|> noneOf "\""
                char '"'
                return $ String x

parseAtom :: Parser LispVal
parseAtom = do
              first <- letter <|> symbol
              rest  <- many (letter <|> digit <|> symbol)
              let atom = first : rest
              return $ case atom of
                            "#t" -> Bool True
                            "#f" -> Bool False
                            _    -> Atom atom

parseNumber :: Parser LispVal
parseNumber = liftM (Number . read) (many1 digit)

unpackNum :: LispVal -> Integer
unpackNum (Number n) = n
unpackNum (String n) = if null parsed then 0 else fst $ head parsed
        where parsed = reads n :: [(Integer, String)]

parseCharacter :: Parser LispVal
parseCharacter = do
                   try $ string "#\\"
                   value <- try (string "newline" <|> string "space")
                        <|> do
                              x <- anyChar
                              notFollowedBy alphaNum
                              return [x]
                   return $ Character $ case value of
                                             "space"   -> ' '
                                             "newline" -> '\n'
                                             _         -> head value

parseList :: Parser LispVal
parseList = liftM List $ sepBy parseExpr spaces

parseDottedList :: Parser LispVal
parseDottedList = do
                    first <- endBy parseExpr spaces
                    rest  <- char '.' >> spaces >> parseExpr
                    return $ DottedList first rest

quoteParser :: Char -> String -> Parser LispVal
quoteParser c s = do
                    char c
                    x <- parseExpr
                    return $ List [Atom s, x]

parseQuoted :: Parser LispVal
parseQuoted = quoteParser '\'' "quote"

-- parseQuasiQuoted :: Parser LispVal
-- parseQuasiQuoted = quoteParser '`' "quasiquote"
--
-- parseUnQuoted :: Parser LispVal
-- parseUnQuoted = quoteParser ',' "unquote"

parseExpr :: Parser LispVal
parseExpr = parseAtom
        <|> parseString
        <|> parseNumber
        <|> parseCharacter
        <|> parseQuoted
--        <|> parseQuasiQuoted
--        <|> parseUnQuoted
        <|> do
              char '('
              x <- try parseList <|> parseDottedList
              char ')'
              return x

-- }}}
-- Types
-- {{{

data LispVal = Atom       String
             | List       [LispVal]
             | DottedList [LispVal] LispVal
             | Number     Integer
             | String     String
             | Bool       Bool
             | Character  Char
             deriving Show

--- }}}
-- Evaluation
-- {{{

eval :: LispVal -> LispVal
eval val@(String _)             = val
eval val@(Number _)             = val
eval val@(Bool _)               = val
eval (List [Atom "quote", val]) = val

readExpr :: String -> LispVal
readExpr input = case parse parseExpr "lisp" input of
                      Left  err -> String $ "No match: " ++ show err
                      Right val -> val

main :: IO ()
main = getArgs >>= print . eval . readExpr . head
