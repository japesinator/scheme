{-# OPTIONS_GHC -fno-warn-warnings-deprecations #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Control.Applicative hiding ((<|>), many)
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
escapedChars = char '\\' *> oneOf "\\\"nrt" >>=
                 \x -> pure $ case x of 'n' -> '\n'
                                        'r' -> '\r'
                                        't' -> '\t'
                                        _   -> x

parseString :: Parser LispVal
parseString = do _ <- char '"'
                 x <- many $ escapedChars <|> noneOf "\""
                 _ <- char '"'
                 pure $ String x

parseAtom :: Parser LispVal
parseAtom = liftA2 (:) (letter <|> symbol)
                       (many (letter <|> digit <|> symbol)) >>=
              \atom -> pure $ if | atom == "#t" -> Bool True
                                 | atom == "#f" -> Bool False
                                 | otherwise    -> Atom atom

parseNumber :: Parser LispVal
parseNumber = Number . read <$> many1 digit

parseCharacter :: Parser LispVal
parseCharacter = do
  _ <- try (string "#\\")
  value <- try $ string "newline"
             <|> string "space"
             <|> (anyChar >>= (notFollowedBy alphaNum *>) . pure . return)
  pure . Character $ case value of
                          "space"   -> ' '
                          "newline" -> '\n'
                          _         -> head value

parseList :: Parser LispVal
parseList = List <$> sepBy parseExpr spaces

parseDottedList :: Parser LispVal
parseDottedList = do first <- endBy parseExpr spaces
                     rest  <- char '.' *> spaces *> parseExpr
                     pure $ DottedList first rest

quoteParser :: Char -> String -> Parser LispVal
quoteParser = flip (fmap . (List .) . (. pure) . (:) . Atom)
                . (*> parseExpr) . char

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
               pure x

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
             deriving (Eq, Show)

--- }}}
-- Evaluation
-- {{{

eval :: Env -> LispVal -> IOThrowsError LispVal
eval _   val@(String _)                      = pure val
eval _   val@(Number _)                      = pure val
eval _   val@(Bool _)                        = pure val
eval env (Atom i)                            = getVar env i
eval _   (List [Atom "quote", val])          = pure val
eval env (List [Atom "if", pr, conseq, alt]) = eval env pr >>= \case
  Bool True  -> eval env conseq
  Bool False -> eval env alt
  _          -> throwError $ TypeMismatch "bool" pr
eval env (List [Atom "set!", Atom var, form])   = eval env form >>=
  setVar env var
eval env (List [Atom "define", Atom var, form]) = eval env form >>=
  defineVar env var
eval env form@(List (Atom "cond" : clauses)) =
  if null clauses
  then throwError $ BadSpecialForm "no true clause in cond expression: " form
  else case head clauses of
            List [Atom "else", expr] -> eval env expr
            List [test, expr] -> eval env $
                                   List [ Atom "if"
                                        , test
                                        , expr
                                        , List (Atom "cond" : tail clauses)
                                        ]
            _ -> throwError $ BadSpecialForm "ill-formed cond expression: " form
eval env (List (Atom func : args)) = mapM (eval env) args >>=
  liftThrows . apply func
eval _ badForm = throwError $ BadSpecialForm "Unrecognized special form" badForm

apply :: String -> [LispVal] -> ThrowsError LispVal
apply func args = maybe
  (throwError $ NotFunction "Unrecognized primitive function args" func)
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

numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] ->
  ThrowsError LispVal
numericBinop _ []      = throwError $ NumArgs 2 []
numericBinop _ [x]     = throwError $ NumArgs 2 [x]
numericBinop op params = Number . foldl1 op <$> mapM unpackNum params

boolBinop :: (LispVal -> ThrowsError a) -> (a -> a -> Bool) -> [LispVal] ->
  ThrowsError LispVal
boolBinop unpacker op args = if length args /= 2
                             then throwError $ NumArgs 2 args
                             else do left  <- unpacker $ head args
                                     right <- unpacker $ last args
                                     pure $ Bool $ left `op` right

numBoolBinop :: (Integer -> Integer -> Bool) -> [LispVal] -> ThrowsError LispVal
numBoolBinop = boolBinop unpackNum

strBoolBinop :: (String -> String -> Bool) -> [LispVal] -> ThrowsError LispVal
strBoolBinop = boolBinop unpackStr

boolBoolBinop :: (Bool -> Bool -> Bool) -> [LispVal] -> ThrowsError LispVal
boolBoolBinop = boolBinop unpackBool

unpackNum :: LispVal -> ThrowsError Integer
unpackNum (Number n) = pure n
unpackNum (String n) = let parsed = reads n in
                           if null parsed
                           then throwError . TypeMismatch "number" $ String n
                           else pure . fst $ head parsed
unpackNum (List [n]) = unpackNum n
unpackNum notNum     = throwError $ TypeMismatch "number" notNum

unpackStr :: LispVal -> ThrowsError String
unpackStr (String s) = pure s
unpackStr (Number s) = pure $ show s
unpackStr (Bool s)   = pure $ show s
unpackStr notString  = throwError $ TypeMismatch "string" notString

unpackBool :: LispVal -> ThrowsError Bool
unpackBool (Bool b) = pure b
unpackBool notBool  = throwError $ TypeMismatch "boolean" notBool

unaryOp :: (LispVal -> LispVal) -> [LispVal] -> ThrowsError LispVal
unaryOp f [v] = pure $ f v
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
car [List (x : _)]          = pure x
car [DottedList (x : _) _]  = pure x
car [badArg]                = throwError $ TypeMismatch "pair" badArg
car badArgList              = throwError $ NumArgs 1 badArgList

cdr :: [LispVal] -> ThrowsError LispVal
cdr [List (_ : xs)]         = pure $ List xs
cdr [DottedList [_] x]      = pure x
cdr [DottedList (_ : xs) x] = pure $ DottedList xs x
cdr [badArg]                = throwError $ TypeMismatch "pair" badArg
cdr badArgList              = throwError $ NumArgs 1 badArgList

cons :: [LispVal] -> ThrowsError LispVal
cons [x1, List []]            = pure $ List [x1]
cons [x, List xs]             = pure . List $ x : xs
cons [x, DottedList xs xlast] = pure $ DottedList (x : xs) xlast
cons [x1, x2]                 = pure $ DottedList [x1] x2
cons badArgList               = throwError $ NumArgs 2 badArgList

eqv :: [LispVal] -> ThrowsError LispVal
eqv [a, b]     = pure . Bool $ a == b
eqv badArgList = throwError $ NumArgs 2 badArgList

data Unpacker = forall a. Eq a => AnyUnpacker (LispVal -> ThrowsError a)

unpackEquals :: LispVal -> LispVal -> Unpacker -> ThrowsError Bool
unpackEquals arg1 arg2 (AnyUnpacker unpacker) = do unpacked1 <- unpacker arg1
                                                   unpacked2 <- unpacker arg2
                                                   pure $ unpacked1 == unpacked2
                                                 `catchError` const (pure False)

eqvList :: ([LispVal] -> ThrowsError LispVal) -> [LispVal] -> ThrowsError LispVal
eqvList eqvFunc [List arg1, List arg2] = pure . Bool $
  (length arg1 == length arg2) && all eqvPair (zip arg1 arg2)
    where eqvPair (x1, x2) = case eqvFunc [x1, x2] of
                                  Left _           -> False
                                  Right (Bool val) -> val
                                  _                -> error "eqvList failed"
eqvList _ _ = error "Bad arguments given to eqvList"

equal :: [LispVal] -> ThrowsError LispVal
equal [List arg1, List arg2]             = eqvList equal [List arg1, List arg2]
equal [DottedList xs x, DottedList ys y] = equal [ List $ xs ++ [x]
                                                 , List $ ys ++ [y]
                                                 ]
equal [arg1, arg2] = do primitiveEquals <- or <$> mapM (unpackEquals arg1 arg2)
                                                       [ AnyUnpacker unpackNum
                                                       , AnyUnpacker unpackStr
                                                       , AnyUnpacker unpackBool
                                                       ]
                        eqvEquals <- eqv [arg1, arg2]
                        pure . Bool $ primitiveEquals
                                   || (\(Bool x) -> x) eqvEquals
equal badArgList = throwError $ NumArgs 2 badArgList

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
                      Right val -> pure val

-- }}}
-- Environment
-- {{{

type Env = IORef [(String, IORef LispVal)]

nullEnv :: IO Env
nullEnv = newIORef []

type IOThrowsError = ErrorT LispError IO

liftThrows :: ThrowsError a -> IOThrowsError a
liftThrows (Left err)  = throwError err
liftThrows (Right val) = pure val

runIOThrows :: IOThrowsError String -> IO String
runIOThrows = liftA (\(Right a) -> a) . runErrorT . trapError

isBound :: Env -> String -> IO Bool
isBound = flip (fmap . (isJust .) . lookup) . readIORef

getVar :: Env -> String -> IOThrowsError LispVal
getVar envRef var = maybe
  (throwError $ UnboundVar "Getting an unbound variable" var)
  (liftIO . readIORef) . lookup var =<< liftIO (readIORef envRef)

setVar :: Env -> String -> LispVal -> IOThrowsError LispVal
setVar envRef var value = liftIO (readIORef envRef) >>=
    maybe (throwError $ UnboundVar "Setting an unbound variable" var)
          (liftIO . (`writeIORef` value)) . lookup var >> pure value

defineVar :: Env -> String -> LispVal -> IOThrowsError LispVal
defineVar envRef var value = do
  alreadyDefined <- liftIO $ isBound envRef var
  if alreadyDefined then setVar envRef var value >> return value
                    else liftIO $ liftA2 ((writeIORef envRef .) . (:) . (var,))
                                         (newIORef value) (readIORef envRef)
                               *> pure value

bindVars :: Env -> [(String, LispVal)] -> IO Env
bindVars envRef = (>>= newIORef) . (readIORef envRef >>=)
                . flip (fmap . flip (++))
                . mapM (uncurry $ flip ((>>=) . newIORef) . (pure .) . (,))

-- }}}
-- REPL
-- {{{

evalAndPrint :: Env -> String -> IO ()
evalAndPrint env = (>>= putStrLn) . runIOThrows . fmap show . (>>= eval env)
                 . liftThrows . readExpr

runRepl :: IO ()
runRepl = nullEnv >>= ((hFlush stdout *> putStr "Lisp>*> " *> getLine) >>=)
        . liftA2 unless (liftA2 (||) (":quit" ==) ("q" ==))
        . ((*> runRepl) .) . evalAndPrint

-- }}}

main :: IO ()
main = length <$> getArgs >>= \case
  0 -> runRepl
  1 -> head <$> getArgs >>= (nullEnv >>=) . flip evalAndPrint
  _ -> putStrLn "Program takes only 0 or 1 argument"
