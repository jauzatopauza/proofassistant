module Parser where 

import Text.Parsec 
import Text.Parsec.String 
import Text.Parsec.Expr 
import Text.Parsec.Token 
import Text.Parsec.Language 
import Logic 
import Proof
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

termsParser :: Parser [Term]
termsParser = do first <- termParser 
                 rest <- remainingTerms 
                 return $ first:rest 

termParser :: Parser Term 
termParser = try (do func <- m_identifier 
                     Func func <$> m_parens termsParser) 
             <|> (Var <$> m_identifier)

remainingTerms :: Parser [Term]
remainingTerms = (char ',' >> spaces >> termsParser) <|> return []

-- z kwantyfikatorami
mainParser :: Parser Formula 
mainParser =    m_whiteSpace >>
               ((do m_reserved "QU"
                    x <- m_identifier 
                    QU x <$> mainParser)
            <|> (do m_reserved "QE"
                    x <- m_identifier 
                    QE x <$> mainParser)
            <|> propParser)

parseFormula :: String -> Either String Formula 
parseFormula s = case parse mainParser "" s of 
                    Left err -> Left $ show err
                    Right phi -> Right phi 

-- gdy nie ma dowodu 
initialCommandParser :: Parser (Location, String)
initialCommandParser = string "prove " >> many1 ident >>= \name -> mainParser >>= \phi -> return (proof [] phi, name)

-- gdy istnieje dowód
activeCommandParser :: [(String, Theorem)] -> Location -> Parser (Either String Location)
activeCommandParser thms loc 
                        = choice [try (string "intro_imp ") >> many1 alphaNum >>= \name -> return $ introImp name loc,
                                  try (string "intro_qu")  >> return (introForall loc),
                                  try (string "intro_and") >> return (introAnd loc),
                                  try (string "intro_or ")  >> 
                                               ((string "left" >> return (introOr loc True)) 
                                            <|> (string "right" >> return (introOr loc False))),
                                  try (string "intro_qe ") >> termParser >>= \term -> return (introExists loc term),
                                  do try $ string "elim_qu " 
                                     varname <- many ident 
                                     m_whiteSpace
                                     term <- termParser 
                                     phi <- mainParser
                                     return $ elimForall loc varname term phi,
                                  try (string "elim_imp ") >> mainParser >>= \phi -> return (elimImp loc phi),
                                  try (string "elim_bot ") >> return (elimSpike loc),
                                  try (string "elim_and ") >> mainParser >>= (\phi ->  (string "left" >> return (elimAnd loc phi True))
                                                                                    <|> (string "right" >> return (elimAnd loc phi False))),
                                  try (string "elim_or ") >> mainParser >>= (\phi -> do  assm1 <- many1 ident 
                                                                                         mainParser >>= (\psi -> do  assm2 <- many1 ident 
                                                                                                                     return (elimOr loc phi assm1 psi assm2))),
                                  try (string "elim_qe ") >> mainParser >>= (\phi -> do  var <- many1 ident 
                                                                                         m_whiteSpace
                                                                                         assm  <- many1 ident 
                                                                                         return $ elimExists loc phi var assm),
                                  try (string "apply_assm ") >> many1 ident >>= \assm -> return (readyByAssumption loc assm),
                                  try (string "apply_thm ") >> many1 ident >>= \thmname -> case lookup thmname thms of 
                                                                                            Just thm -> return (readyByTheorem loc thm)
                                                                                            Nothing -> return $ Left "eval fail",
                                  try (string "equiv ") >> mainParser >>= (return . equivRule loc),
                                  try (string "uncons") >> return (Right (Proof.uncons loc)),
                                  string "abandon" >> return (Left "ABANDONED")] 

parseCommand :: [(String, Theorem)] -> Location -> String -> Either String Location
parseCommand thms loc cmd = case parse (activeCommandParser thms loc) "" cmd of 
                                Left err -> Left $ show err 
                                Right res -> res

parseInitCommand :: String -> Either String (Location, String) 
parseInitCommand cmd = case parse initialCommandParser "" cmd of 
                        Left err -> Left $ show err 
                        Right res -> Right res 
