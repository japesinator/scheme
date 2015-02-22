{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Control.Monad
import Control.Monad.Error
import System.Environment
import Text.ParserCombinators.Parsec hiding (spaces)

-- Parsing
-- {{{

symbol :: Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

spaces :: Parser ()
spaces = skipMany1 space

escapedChars :: Parser Char
escapedChars = do char '\\'
                  x <- oneOf "\\\"nrt"
                  return $ case x of
                                'n' -> '\n'
                                'r' -> '\r'
                                't' -> '\t'
                                _   -> x

parseString :: Parser LispVal
parseString = do char '"'
                 x <- many $ escapedChars <|> noneOf "\""
                 char '"'
                 return $ String x

parseAtom :: Parser LispVal
parseAtom = do first <- letter <|> symbol
               rest  <- many (letter <|> digit <|> symbol)
               let atom = first : rest
               return $ case atom of
                 "#t" -> Bool True
                 "#f" -> Bool False
                 _    -> Atom atom

parseNumber :: Parser LispVal
parseNumber = liftM (Number . read) (many1 digit)

parseCharacter :: Parser LispVal
parseCharacter = do try $ string "#\\"
                    value <- try (string "newline" <|> string "space")
                             <|> do x <- anyChar
                                    notFollowedBy alphaNum
                                    return [x]
                    return $ Character $ case value of
                                              "space"   -> ' '
                                              "newline" -> '\n'
                                              _         -> head value

parseList :: Parser LispVal
parseList = liftM List $ sepBy parseExpr spaces

parseDottedList :: Parser LispVal
parseDottedList = do first <- endBy parseExpr spaces
                     rest  <- char '.' >> spaces >> parseExpr
                     return $ DottedList first rest

quoteParser :: Char -> String -> Parser LispVal
quoteParser c s = do char c
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
        <|> do char '('
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

eval :: LispVal -> ThrowsError LispVal
eval val@(String _) = return val
eval val@(Number _) = return val
eval val@(Bool _) = return val
eval (List [Atom "quote", val]) = return val
eval (List (Atom func : args)) = mapM eval args >>= apply func
eval badForm = throwError $ BadSpecialForm "Unrecognized special form" badForm

apply :: String -> [LispVal] -> ThrowsError LispVal
apply func args = maybe (throwError $ NotFunction "Unrecognized primitive function args" func)
                        ($ args)
                        (lookup func primitives)

primitives :: [(String, [LispVal] -> ThrowsError LispVal)]
primitives = [ ("+",              numericBinop (+))
             , ("-",              numericBinop (-))
             , ("*",              numericBinop (*))
             , ("/",              numericBinop div)
             , ("mod",            numericBinop mod)
             , ("quotient",       numericBinop quot)
             , ("remainder",      numericBinop rem)
             , ("symbol?",        unaryOp      symbolp)
             , ("string?",        unaryOp      stringp)
             , ("number?",        unaryOp      numberp)
             , ("bool?",          unaryOp      boolp)
             , ("list?",          unaryOp      listp)
             , ("symbol2string?", unaryOp      symbol2string)
             , ("string2symbol?", unaryOp      string2symbol)
             ]

numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] -> ThrowsError LispVal
numericBinop _            []  = throwError $ NumArgs 2 []
numericBinop _  singleVal@[_] = throwError $ NumArgs 2 singleVal
numericBinop op params        = liftM (Number . foldl1 op) (mapM unpackNum params)

unpackNum :: LispVal -> ThrowsError Integer
unpackNum (Number n) = return n
unpackNum (String n) = let parsed = reads n in
                           if null parsed
                           then throwError $ TypeMismatch "number" $ String n
                           else return $ fst $ head parsed
unpackNum (List [n]) = unpackNum n
unpackNum notNum     = throwError $ TypeMismatch "number" notNum

unaryOp :: (LispVal -> LispVal) -> [LispVal] -> ThrowsError LispVal
unaryOp f [v] = return $ f v

symbolp, numberp, stringp, boolp, listp :: LispVal -> LispVal
symbolp (Atom _)         = Bool True
symbolp _                = Bool False
numberp (Number _)       = Bool True
numberp _                = Bool False
stringp (String _)       = Bool True
stringp _                = Bool False
boolp   (Bool _)         = Bool True
boolp   _                = Bool False
listp   (List _)         = Bool True
listp   (DottedList _ _) = Bool True
listp   _                = Bool False

symbol2string, string2symbol :: LispVal -> LispVal
symbol2string (Atom s)   = String s
symbol2string _          = String ""
string2symbol (String s) = Atom s
string2symbol _          = Atom ""

-- }}}
-- Errors
-- {{{

data LispError = NumArgs        Integer [LispVal]
               | TypeMismatch   String LispVal
               | Parser         ParseError
               | BadSpecialForm String LispVal
               | NotFunction    String String
               | UnboundVar     String String
               | Default        String

showError :: LispError -> String
showError (UnboundVar message varname)  = message ++ ": " ++ varname
showError (BadSpecialForm message form) = message ++ ": " ++ show form
showError (NotFunction message func)    = message ++ ": " ++ show func
showError (NumArgs expected found)      = "Expected " ++ show expected
                                       ++ " args; found values " ++ (unwords . map show) found
showError (TypeMismatch expected found) = "Invalid type: expected " ++ expected
                                       ++ ", found " ++ show found
showError (Parser parseErr)             = "Parse error at " ++ show parseErr

instance Show LispError where show = showError

instance Error LispError where
  noMsg = Default "An error has occurred"
  strMsg = Default

type ThrowsError = Either LispError

trapError :: forall e (m :: * -> *). (Show e, MonadError e m) => m String -> m String
trapError action = catchError action (return . show)

extractValue :: ThrowsError a -> a
extractValue (Right val) = val

readExpr :: String -> ThrowsError LispVal
readExpr input = case parse parseExpr "lisp" input of
                      Left err  -> throwError $ Parser err
                      Right val -> return val

-- }}}

main :: IO ()
main = do args <- getArgs
          let evaled = liftM show $ readExpr (head args) >>= eval
          putStrLn $ extractValue $ trapError evaled
