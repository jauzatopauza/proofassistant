module Parser where 

import Text.Parsec 
import Text.Parsec.String 
import Text.Parsec.Expr 
import Text.Parsec.Token 
import Text.Parsec.Language 
import Logic 
import Data.Char (isSpace)

ident :: Parser Char
ident = satisfy $ \c -> not (isSpace c || c `elem` ",()")

def = emptyDef {
    identStart = ident,    -- letter
    identLetter = ident,   -- alphaNum
    opStart = oneOf "_|&=",
    opLetter = oneOf "_|&=>",
    reservedOpNames = ["_|_", "|", "&", "=>"],
    reservedNames = ["QU", "QE"]
}

TokenParser {
    parens = m_parens,
    identifier = m_identifier,
    reservedOp = m_reservedOp,
    reserved = m_reserved,
    commaSep = m_commaSep,
    whiteSpace = m_whiteSpace
} = makeTokenParser def 

-- bez kwantyfikatorów
propParser :: Parser Formula
propParser = buildExpressionParser table term <?> "expression"
    where 
    table = [[Infix  (m_reservedOp "&"  >> return (flip Binop And)) AssocLeft ],
             [Infix  (m_reservedOp "|"  >> return (flip Binop Or )) AssocLeft ],
             [Infix  (m_reservedOp "=>" >> return (flip Binop Imp)) AssocRight]]
    term = m_parens mainParser 
           <|> (m_reservedOp "_|_" >> return Spike)
           <|> do rel <- m_identifier 
                  terms <- m_parens termsParser
                  return $ Rel rel terms
    termsParser = do first <- termParser 
                     rest <- remainingTerms 
                     return $ first:rest 
    termParser = try (do func <- m_identifier 
                         Func func <$> m_parens termsParser) 
                 <|> (Var <$> m_identifier)
    remainingTerms = (char ',' >> spaces >> termsParser) <|> return []

-- z kwantyfikatorami
mainParser :: Parser Formula 
mainParser =    (do m_reserved "QU"
                    x <- m_identifier 
                    QU x <$> mainParser)
            <|> (do m_reserved "QE"
                    x <- m_identifier 
                    QE x <$> mainParser)
            <|> propParser 

parseFormula :: String -> Either String Formula 
parseFormula s = case parse mainParser "" s of 
                    Left err -> Left $ show err
                    Right phi -> Right phi 
