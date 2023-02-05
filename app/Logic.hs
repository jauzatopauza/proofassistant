module Logic where

import GHC.Base ( Applicative(liftA2) )
import qualified Data.Map as Map
import qualified Data.List as List

data Formula = 
      Rel String [Term]
    | Spike                                   -- jedyny bezargumentowy spójnik
    | Binop Formula BinaryConnective Formula  -- spójniki binarne w wyliczeniu BinaryConnective
    | QE String Formula                       -- kwantyfikator egzystencjalny
    | QU String Formula                       -- kwantyfikator uniwersalny
    deriving Show

data Term = 
      Var String  
    | Func String [Term]
    deriving Show

data BinaryConnective = And | Or | Imp deriving Show

type Theorem = ([Formula], Formula)

assumptions :: Theorem -> [Formula]
assumptions = fst

consequence :: Theorem -> Formula 
consequence = snd 

class Theory t where 
  axiom :: t -> Formula 

--- zmienne wolne
freeInTerm :: String -> Term -> Bool
freeInTerm var (Var varname) = var == varname 
freeInTerm var (Func _ terms) = any (freeInTerm var) terms 

freeInFormula :: String -> Formula -> Bool 
freeInFormula var (Rel _ terms) = any (freeInTerm var) terms
freeInFormula var Spike = False 
freeInFormula var (Binop phi _ psi) = freeInFormula var phi || freeInFormula var psi 
freeInFormula var (QE varname phi) = if var == varname then False else freeInFormula var phi 
freeInFormula var (QU varname phi) = if var == varname then False else freeInFormula var phi 

--- podstawienie
substInTerm :: Term -> String -> Term -> Term
substInTerm term var t@(Var varname) = if var == varname then term else t
substInTerm term var (Func f terms) = Func f $ map (substInTerm term var) terms 

-- Podstawienie jest niedopuszczalne, jeśli w formule (Q_ s phi) za pewną zmienną y
-- podstawić chcemy term mający wystąpienia s. 
substInFormula :: Formula -> String -> Term -> Maybe Formula 
substInFormula (Rel r terms) var term = Just $ Rel r $ map (substInTerm term var) terms 
substInFormula Spike var term = Just Spike 
substInFormula (Binop phi op psi) var term = liftA2 (flip Binop op) (substInFormula phi var term) (substInFormula psi var term)
substInFormula f@(QE varname phi) var term
  | varname == var = Just f
  | freeInTerm varname term = Nothing
  | otherwise = Just (QE varname) <*> substInFormula phi var term
substInFormula f@(QU varname phi) var term
  | varname == var = Just f
  | freeInTerm varname term = Nothing
  | otherwise = Just (QE varname) <*> substInFormula phi var term

--- równość
eqMapTerms :: [Term] -> [Term] -> Map.Map String String -> Bool 
eqMapTerms [] [] _ = True 
eqMapTerms [] (x:_) _ = False 
eqMapTerms (x:_) [] _ = False 
eqMapTerms (Var x:xs) (Var y:ys) m = (case Map.lookup x m of 
                                      Nothing -> x == y         -- Zmiennych wolnych nie gromadzimy w słowniku, stosujemy na nich równość dosłowną.
                                      Just y' -> y' == y) 
                                      && eqMapTerms xs ys m
eqMapTerms (Var _:_) (Func _ _:_) _ = False 
eqMapTerms (Func f terms1:xs) (Func g terms2:ys) m = (case Map.lookup f m of -- Zakładamy, że sygnatura jest rozłączna ze zbiorem zmiennych. 
                                                      Nothing -> f == g  
                                                      Just g' -> g' == g)
                                                      && eqMapTerms terms1 terms2 m 
                                                      && eqMapTerms xs ys m 
eqMapTerms (Func _ _:_) (Var _:_) _ = False 

eqMap :: Formula -> Formula -> Map.Map String String -> Bool 
eqMap Spike Spike _ = True 
eqMap Spike _ _ = False 
eqMap (Rel r terms1) (Rel s terms2) m = (r == s) && eqMapTerms terms1 terms2 m 
eqMap (Rel _ _) _ _ = False 
eqMap (Binop phi1 _ psi1) (Binop phi2 _ psi2) m = eqMap phi1 phi2 m && eqMap phi2 psi2 m 
eqMap (Binop {}) _ _ = False 
eqMap (QE x phi) (QE y psi) m = eqMap phi psi $ Map.insertWithKey (\ x y z -> y) x y m   -- Skrajny przykład: ∀x R(x) ∧ (∃x H(x)) == ∀x R(x) ∧ (∃y H(y))
eqMap (QE _ _) _ _ = False 
eqMap (QU x phi) (QU y psi) m = eqMap phi psi $ Map.insertWithKey (\ x y z -> y) x y m
eqMap (QU _ _) _ _ = False 

instance Eq Formula where 
  phi == psi = eqMap phi psi Map.empty

--- Reguły dowodzenia od liści do korzenia
ax :: Theory t => t -> Theorem 
ax t = ([], axiom t)

byAssumption :: Formula -> Theorem 
byAssumption phi = ([phi], phi)

impI :: Formula -> Theorem -> Theorem 
impI ant csq = (List.filter (/= ant) (assumptions csq), Binop ant Imp (consequence csq))

impE :: Theorem -> Theorem -> Either String Theorem
impE (gamma, Binop phi Imp psi) (delta, phi') = if phi == phi' 
                                                  then Right (List.union gamma delta, psi)
                                                  else Left "impE: antecedent mismatch"
impE _ _ = Left "impE: nothing to eliminate" 

spikeE :: Formula -> Theorem -> Either String Theorem
spikeE phi (gamma, Spike) = Right (gamma, phi)
spikeE _ _ = Left "spikeE: nothing to eliminate"

quI :: Theorem -> String -> Either String Theorem 
quI (gamma, phi) s = if any (freeInFormula s) gamma 
                      then Left ("quI: illegal assumptions about " ++ s)
                      else Right (gamma, QU s phi)

quE :: Theorem -> Term -> Either String Theorem 
quE (gamma, QU x phi) term = case substInFormula phi x term of 
                              Nothing -> Left "quE: inadmissible substitution; rename bound variable"
                              Just phi' -> Right (gamma, phi')
quE _ _ = Left "quE: nothing to eliminate"

andI :: Theorem -> Theorem -> Theorem 
andI (gamma, phi) (delta, psi) = (List.union gamma delta, Binop phi And psi)

andE1 :: Theorem -> Either String Theorem 
andE1 (gamma, Binop phi And psi) = Right (gamma, phi)
andE1 _ = Left "andE1: nothing to eliminate"

andE2 :: Theorem -> Either String Theorem 
andE2 (gamma, Binop phi And psi) = Right (gamma, psi)
andE2 _ = Left "andE2: nothing to eliminate"

orI1 :: Theorem -> Formula -> Theorem 
orI1 (gamma, phi) psi = (gamma, Binop phi Or psi)

orI2 :: Theorem -> Formula -> Theorem 
orI2 (gamma, phi) psi = (gamma, Binop psi Or phi)

orE :: Theorem -> Theorem -> Theorem -> Either String Theorem -- założenia: pierwsze tw. jest alternatywą, zaś drugie i trzecie mają ten sam wniosek
orE (gamma, Binop phi Or psi) (delta, xi) (sigma, xi') = if xi == xi' 
                                                          then Right (List.union gamma $ List.union delta' sigma', xi) 
                                                          else Left "orE: conclusion mismatch"
                                                        where delta' = filter (/= phi) delta 
                                                              sigma' = filter (/= psi) sigma 
orE _ _ _ = Left "orE: nothing to eliminate"

{-    Γ ⊢ φ[x/t]
     -------------∃i  Niech φ' := φ[x/t]. Cofamy podstawienie.
       Γ ⊢ ∃x φ      -}
qeI :: Formula -> String -> Term -> Theorem -> Either String Theorem 
qeI phi var term (gamma, phi') 
  | substInFormula phi var term == Just phi' = Right (gamma, QE var phi)
  | otherwise = Left "qeI: formula mismatch"

qeE :: Theorem -> Theorem -> Either String Theorem 
qeE (gamma, QE x phi) (delta, psi)
  | any (freeInFormula x) delta' || freeInFormula x psi = Left $ "qeE: illegal assumptions about " ++ x 
  | otherwise = Right (List.union gamma delta', psi)
  where delta' = filter (/= phi) delta 
qeE _ _ = Left "qeE: nothing to eliminate"

equiv :: Theorem -> Formula -> Either String Theorem 
equiv (gamma, phi) psi 
  | phi == psi = Right (gamma, psi)
  | otherwise = Left "equiv: not equivalent"
