module ThermoParser where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import Data.Void
import ThermoLang

-- ==========================================
-- 1. PARSER INFRASTRUCTURE
-- ==========================================

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "//"
    blockCmnt = L.skipBlockComment "/*" "*/"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

keyword :: String -> Parser String
keyword w = lexeme (string w <* notFollowedBy alphaNumChar)

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many alphaNumChar
    check x = if x `elem` reserved then fail $ "keyword " ++ show x ++ " cannot be an identifier" else return x
    reserved = ["if", "then", "else", "let", "in", "true", "false", 
                "map", "fold", "repeat", "shield", "recover", "log"]

integer :: Parser Int
integer = lexeme L.decimal

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

-- ==========================================
-- 2. TERM PARSERS
-- ==========================================

pTerm :: Parser Term
pTerm = makeExprParser pTermPart operatorTable

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

pIf :: Parser Term
pIf = do
    _ <- keyword "if"
    cond <- pTerm
    _ <- keyword "then"
    t1 <- pTerm
    _ <- keyword "else"
    t2 <- pTerm
    return (If cond t1 t2)

pLet :: Parser Term
pLet = do
    _ <- keyword "let"
    name <- identifier
    _ <- symbol "="
    val <- pTerm
    _ <- keyword "in"
    body <- pTerm
    return (Let name val body)

pMap :: Parser Term
pMap = do
    _ <- keyword "map"
    _ <- symbol "("
    var <- identifier
    _ <- symbol "->"
    body <- pTerm
    _ <- symbol ","
    listExpr <- pTerm
    _ <- symbol ")"
    return (Map var body listExpr)

pFold :: Parser Term
pFold = do
    _ <- keyword "fold"
    _ <- symbol "("
    acc <- identifier
    _ <- symbol ","
    var <- identifier
    _ <- symbol "->"
    body <- pTerm
    _ <- symbol ","
    initExpr <- pTerm
    _ <- symbol ","
    listExpr <- pTerm
    _ <- symbol ")"
    return (Fold acc var body initExpr listExpr)

pRepeat :: Parser Term
pRepeat = do
    _ <- keyword "repeat"
    _ <- symbol "("
    n <- integer
    _ <- symbol ")"
    _ <- symbol "{"
    body <- pTerm
    _ <- symbol "}"
    return (Repeat n body)

pShield :: Parser Term
pShield = do
    _ <- keyword "shield"
    tryExpr <- pTerm
    _ <- keyword "recover"
    fallback <- pTerm
    return (Shield tryExpr fallback)

pLog :: Parser Term
pLog = do
    _ <- keyword "log"
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