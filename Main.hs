{-# OPTIONS_GHC -fno-warn-warnings-deprecations #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase, MultiWayIf, TupleSections #-}

module Main (main) where

import Control.Applicative ((<$>), (*>), pure, liftA2)
import Control.Arrow (second)
import Control.Monad.Error (catchError, Error, ErrorT, forM, join, liftIO,
  liftM2, noMsg, runErrorT, strMsg, throwError, unless)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Maybe (isJust, isNothing)
import System.Environment (getArgs)
import System.IO (Handle, hClose, hFlush, hGetLine, hPrint, hPutStrLn,
  IOMode(..), openFile, stdin, stderr, stdout)
import Text.ParserCombinators.Parsec ((<|>), anyChar, alphaNum, char, digit,
  endBy, letter, many, many1, noneOf, notFollowedBy, oneOf, parse, ParseError,
  Parser, sepBy, skipMany1, space, string, try)

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
parseAtom = do atom <- liftA2 (:) (letter <|> symbol)
                                  (many $ letter <|> digit <|> symbol)
               pure $ if | atom == "#t" -> Bool True
                         | atom == "#f" -> Bool False
                         | otherwise    -> Atom atom

parseNumber :: Parser LispVal
parseNumber = Number . read <$> many1 digit

parseCharacter :: Parser LispVal
parseCharacter = do
  _ <- try (string "#\\")
  value <- try $ string "newline"
             <|> string "space"
             <|> ((notFollowedBy alphaNum *>) . pure . pure =<< anyChar)
  pure . Character $ case value of
                          "space"   -> ' '
                          "newline" -> '\n'
                          _         -> head value

parseList :: Parser LispVal
parseList = List <$> sepBy parseExpr spaces

parseDottedList :: Parser LispVal
parseDottedList = liftA2 DottedList (endBy parseExpr spaces)
                                    (char '.' *> spaces *> parseExpr)

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
             | PrimitiveFunc ([LispVal] -> ThrowsError LispVal)
             | Func [String] (Maybe String) [LispVal] Env
             | IOFunc ([LispVal] -> IOThrowsError LispVal)
             | Port Handle

instance Show LispVal where
  show (Atom a)                = a
  show (List xs)               = show xs
  show (DottedList xs x)       = show $ xs ++ [x]
  show (Number n)              = show n
  show (String s)              = s
  show (Bool b)                = show b
  show (Character c)           = [c]
  show (PrimitiveFunc _)       = "<primitive>"
  show (Func args varargs _ _) = "(lambda (" ++ unwords (map show args) ++
    (case varargs of Nothing  -> ""; Just arg -> " . " ++ arg) ++ ") ...)"
  show (Port _)                = "<IO port>"
  show (IOFunc _)              = "<IO primitive>"

instance Eq LispVal where
  (Atom a)          == (Atom b)          = a  == b
  (List xs)         == (List ys)         = xs == ys
  (DottedList xs x) == (DottedList ys y) = xs == ys && x == y
  (Number n)        == (Number m)        = n  == m
  (String s)        == (String t)        = s  == t
  (Bool b)          == (Bool c)          = b  == c
  (Character c)     == (Character d)     = c  == d
  _                 == _                 = False

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

eval env (List [Atom "set!", Atom var, form])   = eval env form >>=
  setVar env var
eval env (List [Atom "define", Atom var, form]) = eval env form >>=
  defineVar env var

eval env (List (Atom "define" : List (Atom var : ps) : b)) =
  makeFunc Nothing env ps b >>= defineVar env var
eval env (List (Atom "define" : DottedList (Atom var : ps) varargs : b)) =
  makeFunc (Just $ show varargs) env ps b >>= defineVar env var
eval env (List (Atom "lambda" : List ps : b)) = makeFunc Nothing env ps b
eval env (List (Atom "lambda" : DottedList ps varargs : b)) =
  makeFunc (Just $ show varargs) env ps b
eval env (List (Atom "lambda" : varargs@(Atom _) : b)) =
  makeFunc (Just $ show varargs) env ([] :: [LispVal]) b

eval env (List [Atom "load", String filename]) = load filename >>=
  fmap last . mapM (eval env)

eval env (List (function : args))  = join $ liftM2 apply (eval env function)
                                                         (mapM (eval env) args)

eval _ val@(List _)                = pure val

eval _ badForm = throwError $ BadSpecialForm "Unrecognized special form" badForm

makeFunc :: Maybe String -> Env -> [LispVal] -> [LispVal]
         -> IOThrowsError LispVal
makeFunc varargs env ps = pure . flip (Func (map show ps) varargs) env

apply :: LispVal -> [LispVal] -> IOThrowsError LispVal
apply (PrimitiveFunc func) args = liftThrows $ func args
apply (Func ps varargs b c) args =
  if length ps /= length args && isNothing varargs
     then throwError $ NumArgs (toInteger $ length ps) args
     else fmap last . forM b . eval
      =<< bind varargs
      =<< liftIO (bindVars c $ zip ps args)
       where bind arg env = case arg of
               Just argName -> liftIO $ bindVars env
                 [(argName, List $ drop (length ps) args)]
               Nothing      -> pure env
apply (IOFunc func) args = func args
apply _ _ = error "We have somehow applied a non-function"

-- }}}
-- Standard Library
-- {{{

primBindings :: IO Env
primBindings = nullEnv >>= flip bindVars (map (second IOFunc) ioPrimitives
                                       ++ map (second PrimitiveFunc) primitives)

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
             , ("cdr",                          cdr)
             , ("cons",                         cons)
             , ("eq?",                          eqv)
             , ("eqv?",                         eqv)
             , ("equal",                        equal)
             ]

ioPrimitives :: [(String, [LispVal] -> IOThrowsError LispVal)]
ioPrimitives = [ ("apply", applyProc)
               , ("open-input-file", makePort ReadMode)
               , ("open-output-file", makePort WriteMode)
               , ("close-input-port", closePort)
               , ("close-output-port", closePort)
               , ("read", readProc)
               , ("write", writeProc)
               , ("read-contents", readContents)
               , ("read-all", readAll)
               ]

numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] ->
  ThrowsError LispVal
numericBinop _  []  = throwError $ NumArgs 2 []
numericBinop _  [x] = throwError $ NumArgs 2 [x]
numericBinop op ps  = Number . foldl1 op <$> mapM unpackNum ps

boolBinop :: (LispVal -> ThrowsError a) -> (a -> a -> Bool) -> [LispVal] ->
  ThrowsError LispVal
boolBinop unpacker op args = if length args /= 2
                             then throwError $ NumArgs 2 args
                             else Bool <$> liftA2 op (unpacker $ head args)
                                                     (unpacker $ last args)

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

applyProc :: [LispVal] -> IOThrowsError LispVal
applyProc [func, List args] = apply func args
applyProc (func : args)     = apply func args
applyProc _                 = error "Odd type mismatch"

makePort :: IOMode -> [LispVal] -> IOThrowsError LispVal
makePort mode [String filename] = fmap Port . liftIO $ openFile filename mode
makePort _    _                 = error "Odd type mismatch"

closePort :: [LispVal] -> IOThrowsError LispVal
closePort [Port port] = liftIO $ hClose port >> return (Bool True)
closePort _           = return $ Bool False

readProc :: [LispVal] -> IOThrowsError LispVal
readProc []          = readProc [Port stdin]
readProc [Port port] = liftIO (hGetLine port)
                   >>= liftThrows . readOrThrow parseExpr
readProc _           = error "Odd type mismatch"

writeProc :: [LispVal] -> IOThrowsError LispVal
writeProc [obj]            = writeProc [obj, Port stdout]
writeProc [obj, Port port] = liftIO $ hPrint port obj >> return (Bool True)
writeProc _                = error "Odd type mismatch"

readContents :: [LispVal] -> IOThrowsError LispVal
readContents [String filename] = fmap String . liftIO $ readFile filename
readContents _                 = error "Odd type mismatch"

load :: String -> IOThrowsError [LispVal]
load filename = liftIO (readFile filename)
            >>= liftThrows . readOrThrow (endBy parseExpr spaces)

readAll :: [LispVal] -> IOThrowsError LispVal
readAll [String filename] = List <$> load filename
readAll _                 = error "Odd type mismatch"

data Unpacker = forall a. Eq a => AnyUnpacker (LispVal -> ThrowsError a)

unpackEquals :: LispVal -> LispVal -> Unpacker -> ThrowsError Bool
unpackEquals arg1 arg2 (AnyUnpacker unpacker) = liftA2 (==) (unpacker arg1)
                                                            (unpacker arg2)
                                                 `catchError` const (pure False)

eqvList :: ([LispVal] -> ThrowsError LispVal) -> [LispVal]
        -> ThrowsError LispVal
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
equal [arg1, arg2] = do primitiveEquals <- mapM (unpackEquals arg1 arg2)
                                                [ AnyUnpacker unpackNum
                                                , AnyUnpacker unpackStr
                                                , AnyUnpacker unpackBool
                                                ]
                        eqvEquals <- eqv [arg1, arg2]
                        pure . Bool $ or primitiveEquals
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

trapError :: IOThrowsError String -> IOThrowsError String
trapError = flip catchError $ return . show

readOrThrow :: Parser a -> String -> ThrowsError a
readOrThrow p input = case parse p "lisp" input of
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
liftThrows = either throwError pure

runIOThrows :: IOThrowsError String -> IO String
runIOThrows = fmap (\(Right a) -> a) . runErrorT . trapError

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
defineVar envRef var value = liftIO (isBound envRef var) >>= \case
  True  -> setVar envRef var value *> pure value
  False -> liftIO $ do valueRef <- newIORef value
                       env <- readIORef envRef
                       writeIORef envRef ((var, valueRef) : env)
                       pure value

bindVars :: Env -> [(String, LispVal)] -> IO Env
bindVars envRef = (>>= newIORef) . (readIORef envRef >>=)
                . flip (fmap . flip (++))
                . mapM (uncurry $ flip ((>>=) . newIORef) . (pure .) . (,))

-- }}}
-- REPL
-- {{{

evalAndPrint :: Env -> String -> IO ()
evalAndPrint env = (>>= putStrLn) . runIOThrows . fmap show . (>>= eval env)
                 . liftThrows . readOrThrow parseExpr

runOne :: [String] -> Env -> IO ()
runOne args e = do
  env <- bindVars e [("args", List $ map String $ drop 1 args)]
  err <- runIOThrows
    (fmap show . eval env $ List [Atom "load", String $ head args])
  hPutStrLn stderr err

runRepl :: Env -> IO ()
runRepl = tilQuit (putStr "Lisp>>> " *> hFlush stdout *> getLine) . evalAndPrint
  where tilQuit p a = liftA2 unless (== "quit") ((*> tilQuit p a) . a) =<< p

-- }}}

main :: IO ()
main = do args <- getArgs
          primBindings >>= if null args then runRepl else runOne args
