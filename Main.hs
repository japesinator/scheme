{-# OPTIONS_GHC -fno-warn-warnings-deprecations #-}
{-# LANGUAGE ExistentialQuantification #-}

module Main where

import Control.Monad
import Control.Monad.Error
import Data.IORef
import Data.Maybe
import System.Environment
import System.IO
import Text.ParserCombinators.Parsec hiding (spaces)

-- Parsing
-- {{{

symbol :: Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

spaces :: Parser ()
spaces = skipMany1 space

escapedChars :: Parser Char
escapedChars = do _ <- char '\\'
                  x <- oneOf "\\\"nrt"
                  return $ case x of
                                'n' -> '\n'
                                'r' -> '\r'
                                't' -> '\t'
                                _   -> x

parseString :: Parser LispVal
parseString = do _ <- char '"'
                 x <- many $ escapedChars <|> noneOf "\""
                 _ <- char '"'
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
parseNumber = liftM (Number . read) $ many1 digit

parseCharacter :: Parser LispVal
parseCharacter = do _     <- try $ string "#\\"
                    value <- try $ string "newline" <|> string "space"
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
quoteParser c s = do _ <- char c
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
        <|> do _ <- char '('
               x <- try parseList <|> parseDottedList
               _ <- char ')'
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
eval val@(String _)                      = return val
eval val@(Number _)                      = return val
eval val@(Bool _)                        = return val
eval (List [Atom "quote", val])          = return val
eval (List [Atom "if", pr, conseq, alt]) = do result <- eval pr
                                              case result of
                                                Bool True  -> eval conseq
                                                Bool False -> eval alt
                                                _          -> throwError $ TypeMismatch "bool" pr
eval form@(List (Atom "cond" : clauses)) =
  if null clauses
  then throwError $ BadSpecialForm "no true clause in cond expression: " form
  else case head clauses of
            List [Atom "else", expr] -> eval expr
            List [test, expr]        -> eval $ List [ Atom "if"
                                                    , test
                                                    , expr
                                                    , List (Atom "cond" : tail clauses)
                                                    ]
            _                        -> throwError $ BadSpecialForm "ill-formed cond expression: " form
eval (List (Atom func : args))           = mapM eval args >>= apply func
eval badForm                             = throwError $ BadSpecialForm "Unrecognized special form" badForm

apply :: String -> [LispVal] -> ThrowsError LispVal
apply func args = maybe (throwError $ NotFunction "Unrecognized primitive function args" func)
                        ($ args) $ lookup func primitives

primitives :: [(String, [LispVal] -> ThrowsError LispVal)]
primitives = [ ("&&",             boolBoolBinop (&&))
             , ("||",             boolBoolBinop (||))
             , ("=",              numBoolBinop  (==))
             , ("<",              numBoolBinop  (<))
             , (">",              numBoolBinop  (>))
             , ("/=",             numBoolBinop  (/=))
             , (">=",             numBoolBinop  (>=))
             , ("<=",             numBoolBinop  (<=))
             , ("+",              numericBinop  (+))
             , ("-",              numericBinop  (-))
             , ("*",              numericBinop  (*))
             , ("/",              numericBinop  div)
             , ("mod",            numericBinop  mod)
             , ("quotient",       numericBinop  quot)
             , ("remainder",      numericBinop  rem)
             , ("string=?",       strBoolBinop  (==))
             , ("string<?",       strBoolBinop  (<))
             , ("string>?",       strBoolBinop  (>))
             , ("string<=?",      strBoolBinop  (<=))
             , ("string>=?",      strBoolBinop  (>=))
             , ("symbol?",        unaryOp       symbolp)
             , ("string?",        unaryOp       stringp)
             , ("number?",        unaryOp       numberp)
             , ("bool?",          unaryOp       boolp)
             , ("list?",          unaryOp       listp)
             , ("symbol2string?", unaryOp       symbol2string)
             , ("string2symbol?", unaryOp       string2symbol)
             , ("car",                          car)
             , ("cdr",                          car)
             , ("cons",                         cons)
             , ("eq?",                          eqv)
             , ("eqv?",                         eqv)
             , ("equal",                        equal)
             ]

numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] -> ThrowsError LispVal
numericBinop _ []      = throwError $ NumArgs 2 []
numericBinop _ [x]     = throwError $ NumArgs 2 [x]
numericBinop op params = liftM (Number . foldl1 op) $ mapM unpackNum params

boolBinop :: (LispVal -> ThrowsError a) -> (a -> a -> Bool) -> [LispVal] -> ThrowsError LispVal
boolBinop unpacker op args = if length args /= 2
                             then throwError $ NumArgs 2 args
                             else do left  <- unpacker $ head args
                                     right <- unpacker $ last args
                                     return $ Bool $ left `op` right

numBoolBinop :: (Integer -> Integer -> Bool) -> [LispVal] -> ThrowsError LispVal
numBoolBinop  = boolBinop unpackNum

strBoolBinop :: (String -> String -> Bool) -> [LispVal] -> ThrowsError LispVal
strBoolBinop  = boolBinop unpackStr

boolBoolBinop :: (Bool -> Bool -> Bool) -> [LispVal] -> ThrowsError LispVal
boolBoolBinop = boolBinop unpackBool

unpackNum :: LispVal -> ThrowsError Integer
unpackNum (Number n) = return n
unpackNum (String n) = let parsed = reads n in
                           if null parsed
                           then throwError $ TypeMismatch "number" $ String n
                           else return $ fst $ head parsed
unpackNum (List [n]) = unpackNum n
unpackNum notNum     = throwError $ TypeMismatch "number" notNum

unpackStr :: LispVal -> ThrowsError String
unpackStr (String s) = return s
unpackStr (Number s) = return $ show s
unpackStr (Bool s)   = return $ show s
unpackStr notString  = throwError $ TypeMismatch "string" notString

unpackBool :: LispVal -> ThrowsError Bool
unpackBool (Bool b) = return b
unpackBool notBool  = throwError $ TypeMismatch "boolean" notBool

unaryOp :: (LispVal -> LispVal) -> [LispVal] -> ThrowsError LispVal
unaryOp f [v] = return $ f v
unaryOp _ _   = error "Wrong number of arguments given to a unary operation"

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

car :: [LispVal] -> ThrowsError LispVal
car [List (x : _)]          = return x
car [DottedList (x : _) _]  = return x
car [badArg]                = throwError $ TypeMismatch "pair" badArg
car badArgList              = throwError $ NumArgs 1 badArgList

cdr :: [LispVal] -> ThrowsError LispVal
cdr [List (_ : xs)]         = return $ List xs
cdr [DottedList [_] x]      = return x
cdr [DottedList (_ : xs) x] = return $ DottedList xs x
cdr [badArg]                = throwError $ TypeMismatch "pair" badArg
cdr badArgList              = throwError $ NumArgs 1 badArgList

cons :: [LispVal] -> ThrowsError LispVal
cons [x1, List []]            = return $ List [x1]
cons [x, List xs]             = return $ List $ x : xs
cons [x, DottedList xs xlast] = return $ DottedList (x : xs) xlast
cons [x1, x2]                 = return $ DottedList [x1] x2
cons badArgList               = throwError $ NumArgs 2 badArgList

eqv :: [LispVal] -> ThrowsError LispVal
eqv [Bool arg1, Bool arg2]             = return $ Bool $ arg1 == arg2
eqv [Number arg1, Number arg2]         = return $ Bool $ arg1 == arg2
eqv [String arg1, String arg2]         = return $ Bool $ arg1 == arg2
eqv [Atom arg1, Atom arg2]             = return $ Bool $ arg1 == arg2
eqv [DottedList xs x, DottedList ys y] = eqv [List $ xs ++ [x], List $ ys ++ [y]]
eqv [List arg1, List arg2]             = eqvList eqv [List arg1, List arg2]
eqv [_, _]                             = return $ Bool False
eqv badArgList                         = throwError $ NumArgs 2 badArgList

data Unpacker = forall a. Eq a => AnyUnpacker (LispVal -> ThrowsError a)

unpackEquals :: LispVal -> LispVal -> Unpacker -> ThrowsError Bool
unpackEquals arg1 arg2 (AnyUnpacker unpacker) = do unpacked1 <- unpacker arg1
                                                   unpacked2 <- unpacker arg2
                                                   return $ unpacked1 == unpacked2
                                                 `catchError` const (return False)

eqvList :: ([LispVal] -> ThrowsError LispVal) -> [LispVal] -> ThrowsError LispVal
eqvList eqvFunc [List arg1, List arg2] = return $ Bool $ (length arg1 == length arg2) &&
                                                         all eqvPair (zip arg1 arg2)
    where eqvPair (x1, x2) = case eqvFunc [x1, x2] of
                                  Left _           -> False
                                  Right (Bool val) -> val
                                  _                -> error "eqvList failed"
eqvList _       _                      = error "Bad arguments given to eqvList"

equal :: [LispVal] -> ThrowsError LispVal
equal [List arg1, List arg2]             = eqvList equal [List arg1, List arg2]
equal [DottedList xs x, DottedList ys y] = equal [List $ xs ++ [x], List $ ys ++ [y]]
equal [arg1, arg2]                       = do primitiveEquals <- liftM or $ mapM (unpackEquals arg1 arg2)
                                                                                 [ AnyUnpacker unpackNum
                                                                                 , AnyUnpacker unpackStr
                                                                                 , AnyUnpacker unpackBool
                                                                                 ]
                                              eqvEquals <- eqv [arg1, arg2]
                                              return $ Bool $ primitiveEquals || let (Bool x) = eqvEquals in x
equal badArgList                         = throwError $ NumArgs 2 badArgList

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
showError _                             = "Unknown error"

instance Show LispError where show = showError

instance Error LispError where
  noMsg  = Default "An error has occurred"
  strMsg = Default

type ThrowsError = Either LispError

trapError :: (MonadError e m, Show e) => m String -> m String
trapError action = catchError action (return . show)

readExpr :: String -> ThrowsError LispVal
readExpr input = case parse parseExpr "lisp" input of
                      Left err  -> throwError $ Parser err
                      Right val -> return val

-- }}}
-- Environment
-- {{{

type Env = IORef [(String, IORef LispVal)]

nullEnv :: IO Env
nullEnv = newIORef []

type IOThrowsError = ErrorT LispError IO

liftThrows :: ThrowsError a -> IOThrowsError a
liftThrows (Left err)  = throwError err
liftThrows (Right val) = return val

runIOThrows :: IOThrowsError String -> IO String
runIOThrows = liftM extractValue . runErrorT . trapError

isBound :: Env -> String -> IO Bool
isBound envRef var = liftM (isJust . lookup var) (readIORef envRef)

getVar :: Env -> String -> IOThrowsError LispVal
getVar envRef var = maybe (throwError $ UnboundVar "Getting an unbound variable" var)
                    (liftIO . readIORef) . lookup var =<< liftIO (readIORef envRef)
-- }}}
-- REPL
-- {{{

flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

extractValue :: Either a b -> b
extractValue (Right val) = val
extractValue _           = error "Trapping errors failed"

evalString :: String -> IO String
evalString expr = return . extractValue . trapError . liftM show $ readExpr expr >>= eval

evalAndPrint :: String -> IO ()
evalAndPrint expr =  evalString expr >>= putStrLn

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pr prompt action = do result <- prompt
                             unless (pr result) $ action result >> until_ pr prompt action

runRepl :: IO ()
runRepl = until_ (\x -> (x == ":quit") || (x == "q")) (readPrompt "Lisp>>> ") evalAndPrint

-- }}}

main :: IO ()
main = do args <- getArgs
          case length args of
            0 -> runRepl
            1 -> evalAndPrint $ head args
            _ -> putStrLn "Program takes only 0 or 1 argument"
