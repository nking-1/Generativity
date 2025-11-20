module ThermoParser where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import Data.Void
import ThermoLangV2

-- ==========================================
-- 1. PARSER INFRASTRUCTURE
-- ==========================================

type Parser = Parsec Void String

-- Whitespace consumer
sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "//"
    blockCmnt = L.skipBlockComment "/*" "*/"

-- Lexeme wrapper (consumes trailing whitespace)
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- Static symbols
symbol :: String -> Parser String
symbol = L.symbol sc

-- Reserved keywords
keyword :: String -> Parser String
keyword w = lexeme (string w <* notFollowedBy alphaNumChar)

-- Identifiers (variables)
identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many alphaNumChar
    check x = if x `elem` reserved then fail $ "keyword " ++ show x ++ " cannot be an identifier" else return x
    reserved = ["if", "then", "else", "let", "in", "true", "false", 
                "map", "fold", "repeat", "shield", "recover", "log"]

-- Integers
integer :: Parser Int
integer = lexeme L.decimal

-- Parentheses
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

-- ==========================================
-- 2. TERM PARSERS
-- ==========================================

pTerm :: Parser Term
pTerm = makeExprBuilder pTermPart operatorTable

-- The atom of the language
pTermPart :: Parser Term
pTermPart = choice
  [ parens pTerm
  , pIf
  , pLet
  , pMap
  , pFold
  , pRepeat
  , pShield
  , pLog
  , pList
  , pBool
  , pInt
  , pVar
  ]

-- --- PRIMITIVES ---

pInt :: Parser Term
pInt = IntVal <$> integer

pBool :: Parser Term
pBool = (BoolVal True <$ keyword "true")
    <|> (BoolVal False <$ keyword "false")

pVar :: Parser Term
pVar = Var <$> identifier

pList :: Parser Term
pList = do
    items <- brackets (pTerm `sepBy` symbol ",")
    return (ListVal items)

-- --- CONTROL FLOW ---

pIf :: Parser Term
pIf = do
    keyword "if"
    cond <- pTerm
    keyword "then"
    t1 <- pTerm
    keyword "else"
    t2 <- pTerm
    return (If cond t1 t2)

pLet :: Parser Term
pLet = do
    keyword "let"
    name <- identifier
    symbol "="
    val <- pTerm
    keyword "in"
    body <- pTerm
    return (Let name val body)

-- --- DATA PROCESSING ---

-- Syntax: map(var -> body, list)
pMap :: Parser Term
pMap = do
    keyword "map"
    symbol "("
    var <- identifier
    symbol "->"
    body <- pTerm
    symbol ","
    listExpr <- pTerm
    symbol ")"
    return (Map var body listExpr)

-- Syntax: fold(acc, var -> body, init, list)
pFold :: Parser Term
pFold = do
    keyword "fold"
    symbol "("
    acc <- identifier
    symbol ","
    var <- identifier
    symbol "->"
    body <- pTerm
    symbol ","
    initExpr <- pTerm
    symbol ","
    listExpr <- pTerm
    symbol ")"
    return (Fold acc var body initExpr listExpr)

-- --- SPECIAL OPS ---

-- Syntax: repeat(n) { body }
pRepeat :: Parser Term
pRepeat = do
    keyword "repeat"
    symbol "("
    n <- integer
    symbol ")"
    symbol "{"
    body <- pTerm
    symbol "}"
    return (Repeat n body)

-- Syntax: shield expr recover default
pShield :: Parser Term
pShield = do
    keyword "shield"
    tryExpr <- pTerm
    keyword "recover"
    fallback <- pTerm
    return (Shield tryExpr fallback)

pLog :: Parser Term
pLog = do
    keyword "log"
    msg <- lexeme (char '"' >> manyTill L.charLiteral (char '"'))
    val <- pTerm
    return (Log msg val)

-- ==========================================
-- 3. OPERATOR PRECEDENCE
-- ==========================================

operatorTable :: [[Operator Parser Term]]
operatorTable =
  [ [ InfixL (Div <$ symbol "/") ]
  , [ InfixL (Add <$ symbol "+") ]
  , [ InfixL (Eq  <$ symbol "==") ]
  ]

-- ==========================================
-- 4. PUBLIC API
-- ==========================================

parseThermo :: String -> Either String Term
parseThermo input = 
    case parse (sc *> pTerm <* eof) "" input of
        Left bundle -> Left (errorBundlePretty bundle)
        Right term  -> Right term