module SCIParse (readFormula) where
import Text.ParserCombinators.Parsec (Parser(..), parse,
        many, try, between, notFollowedBy, choice, (<|>), (<?>),
        string, char, letter, alphaNum, eof, spaces)
import Control.Monad.Except (liftM2, throwError)
import Control.Monad (void)
import SCITypes (SCIFormula(..), ThrowsError, SCIError(..))
import SCIHelper (BinOp)

parseWord :: Parser String
parseWord = do
    first <- letter
    rest <- many alphaNum
    let x = first:rest in
        if isKW x then fail $ "Illegal identifier: " ++ x else return x

isKW :: String -> Bool
isKW = flip elem [ "not", "and", "or", "implies", "equiv", "ident" ]

parseKeyword :: String -> Parser String
parseKeyword s = string s >> notFollowedBy alphaNum >> return s

parseStrOrKw :: String -> String -> Parser ()
parseStrOrKw s kw = void $ try (string s) <|> try (parseKeyword kw)

parseNot :: Parser SCIFormula
parseNot = Not <$> (parseStrOrKw "~" "not" >> parseUnary)

parseVariable :: Parser SCIFormula
parseVariable = Variable <$> parseWord

parseParen :: Parser SCIFormula
parseParen = between (char '(') (spaces >> char ')') parseFormula

parseUnary :: Parser SCIFormula
parseUnary = spaces >> (parseNot <|> parseVariable <|> parseParen <?> "SCI formula" )

parseBinOp :: Parser (BinOp SCIFormula)

parseBinOp = spaces >> choice
    [ doBinOp "and" "&" And,
      doBinOp "or" "|" Or,
      doBinOp "implies" "->" Imply,
      doBinOp "equiv" "<->" Equiv,
      doBinOp "ident" "=" Ident ]

doBinOp :: String -> String -> BinOp SCIFormula -> Parser (BinOp SCIFormula)
doBinOp kw s op = (parseKeyword kw <|> string s) >> return op

parseBinary :: Parser SCIFormula
parseBinary = do
    x <- parseUnary
    op <- parseBinOp
    op x <$> parseUnary

parseFormula :: Parser SCIFormula
parseFormula = try parseBinary <|> parseUnary

parseFormulaEOF :: Parser SCIFormula
parseFormulaEOF = liftM2 const parseFormula (spaces >> eof)

readFormula :: String -> ThrowsError SCIFormula
readFormula input = case parse parseFormulaEOF "sci" input of
    Left e -> throwError $ SCIParsingError e
    Right v -> return v
