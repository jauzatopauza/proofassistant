module Proof where 
import Logic
import Control.Applicative ( Alternative((<|>)) )
import qualified Data.List as List

type Assumptions = [(String, Formula)]

data Proof = 
      Goal Assumptions Formula
    | Ready Theorem 
    | ImpI Formula Proof  -- poprzednik przechowujemy, następnik z dowodu
    | ImpE Proof Proof    -- dowód implikacji i dowód poprzednika
    | SpikeE Formula Proof
    | QUI String Proof    -- dowód ϕ i nazwa zmiennej kwantyfikowanej
    | QUE Term Proof
    | AndI Proof Proof 
    | AndE1 Proof 
    | AndE2 Proof 
    | OrI1 Formula Proof  -- pierwszy składnik udowodniony, drugi nie wiadomo skąd
    | OrI2 Formula Proof  -- drugi składnik udowodniony, pierwszy nie wiadomo skąd
    | OrE Proof Proof Proof 
    | QEI Formula String Term Proof -- w formule ϕ za zmienną x podstawiamy term t i udowadniamy wynik
    | QEE Proof Proof -- udowadniamy, że coś istnieje, i korzystamy z tego w innym dowodzie; 
    | Equiv Formula Proof   -- nowa formuła równa według (==)

data Path = 
      Root 
    | DownImpI Formula Path 
    | LeftImpE Path Proof 
    | RightImpE Proof Path 
    | DownSpikeE Formula Path 
    | DownQUI String Path 
    | DownQUE Term Path 
    | LeftAndI Path Proof 
    | RightAndI Proof Path 
    | DownAndE1 Path 
    | DownAndE2 Path 
    | DownOrI1 Formula Path 
    | DownOrI2 Formula Path 
    | LeftOrE Path Proof Proof 
    | MiddleOrE Proof Path Proof 
    | RightOrE Proof Proof Path 
    | DownQEI Formula String Term Path 
    | LeftQEE Path Proof 
    | RightQEE Proof Path 
    | DownEquiv Formula Path 

type Location = (Proof, Path)

proof :: Assumptions -> Formula -> Location 
proof gamma phi = (Goal gamma phi, Root)

goal :: Proof -> Maybe (Assumptions, Formula)
goal (Goal gamma phi) = Just (gamma, phi)
goal (Ready _) = Nothing 
goal (ImpI _ pf) = goal pf 
goal (SpikeE _ pf) = goal pf 
goal (QUI _ pf) = goal pf 
goal (QUE _ pf) = goal pf 
goal (AndE1 pf) = goal pf 
goal (AndE2 pf) = goal pf 
goal (OrI1 _ pf) = goal pf 
goal (OrI2 _ pf) = goal pf
goal (QEI _ _ _ pf) = goal pf 
goal (Equiv _ pf) = goal pf 
goal (ImpE pf1 pf2) = goal pf1 <|> goal pf2 
goal (AndI pf1 pf2) = goal pf1 <|> goal pf2 
goal (OrE pf1 pf2 pf3) = goal pf1 <|> goal pf2 <|> goal pf3 
goal (QEE pf1 pf2) = goal pf1 <|> goal pf2 

collapseToTheorem :: Proof -> Either String Theorem 
collapseToTheorem (Goal _ _) = Left "collapseToTheorem: proof incomplete!" 
collapseToTheorem (Ready thm) = Right thm 
collapseToTheorem (ImpI phi pf) = impI phi <$> collapseToTheorem pf 
collapseToTheorem (ImpE pf1 pf2) = do thm1 <- collapseToTheorem pf1 
                                      thm2 <- collapseToTheorem pf2 
                                      impE thm1 thm2
collapseToTheorem (SpikeE phi pf) = collapseToTheorem pf >>= spikeE phi
collapseToTheorem (QUI s pf) = collapseToTheorem pf >>= flip quI s
collapseToTheorem (QUE t pf) = collapseToTheorem pf >>= flip quE t 
collapseToTheorem (AndI pf1 pf2) = do thm1 <- collapseToTheorem pf1 
                                      thm2 <- collapseToTheorem pf2 
                                      return $ andI thm1 thm2 
collapseToTheorem (AndE1 pf) = collapseToTheorem pf >>= andE1 
collapseToTheorem (AndE2 pf) = collapseToTheorem pf >>= andE2 
collapseToTheorem (OrI1 phi pf) = flip orI1 phi <$> collapseToTheorem pf 
collapseToTheorem (OrI2 phi pf) = flip orI2 phi <$> collapseToTheorem pf 
collapseToTheorem (OrE pf1 pf2 pf3) = do thm1 <- collapseToTheorem pf1 
                                         thm2 <- collapseToTheorem pf2 
                                         thm3 <- collapseToTheorem pf3 
                                         orE thm1 thm2 thm3 
collapseToTheorem (QEI phi s t pf) = collapseToTheorem pf >>= qeI phi s t
collapseToTheorem (QEE pf1 pf2) = do thm1 <- collapseToTheorem pf1 
                                     thm2 <- collapseToTheorem pf2 
                                     qeE thm1 thm2 
collapseToTheorem (Equiv phi pf) = collapseToTheorem pf >>= flip equiv phi 

seekDown :: Location -> Maybe Location 
seekDown loc@(Goal _ _, _) = Just loc 
seekDown (Ready _, _) = Nothing 
seekDown (ImpI phi pf, ctx) = seekDown (pf, DownImpI phi ctx)
seekDown (ImpE pf1 pf2, ctx) = seekDown (pf1, LeftImpE ctx pf2) <|> seekDown (pf2, RightImpE pf1 ctx)
seekDown (SpikeE phi pf, ctx) = seekDown (pf, DownSpikeE phi ctx)
seekDown (QUI s pf, ctx) = seekDown (pf, DownQUI s ctx)
seekDown (QUE t pf, ctx) = seekDown (pf, DownQUE t ctx)
seekDown (AndI pf1 pf2, ctx) = seekDown (pf1, LeftAndI ctx pf2) <|> seekDown (pf2, RightAndI pf1 ctx)
seekDown (AndE1 pf, ctx) = seekDown (pf, DownAndE1 ctx)
seekDown (AndE2 pf, ctx) = seekDown (pf, DownAndE2 ctx)
seekDown (OrI1 phi pf, ctx) = seekDown (pf, DownOrI1 phi ctx)
seekDown (OrI2 phi pf, ctx) = seekDown (pf, DownOrI2 phi ctx)
seekDown (OrE pf1 pf2 pf3, ctx) =   seekDown (pf1, LeftOrE   ctx pf2 pf3) 
                                <|> seekDown (pf2, MiddleOrE pf1 ctx pf3) 
                                <|> seekDown (pf3, RightOrE  pf1 pf2 ctx)
seekDown (QEI phi s t pf, ctx) = seekDown (pf, DownQEI phi s t ctx)
seekDown (QEE pf1 pf2, ctx) = seekDown (pf1, LeftQEE ctx pf2)
seekDown (Equiv phi pf, ctx) = seekDown (pf, DownEquiv phi ctx)

wrap :: Path -> Theorem -> Either String Location 
wrap ctx thm = seekUp (Ready thm, ctx)

caseDown :: Proof -> Path -> (Proof -> Proof) -> Either String Location
caseDown pf ctx cnt = case pf of 
                        Ready _ -> collapseToTheorem (cnt pf) >>= wrap ctx 
                        _       -> Right (cnt pf, ctx)

seekUp :: Location -> Either String Location 
seekUp (pf, Root) = Right (pf, Root)
seekUp (pf, DownImpI phi ctx) = caseDown pf ctx (ImpI phi)
seekUp (pf1, LeftImpE ctx pf2) = case seekDown (pf2, RightImpE pf1 ctx) of 
                                  Just loc -> Right loc
                                  Nothing  -> collapseToTheorem pf2 >>= \thm -> seekUp (Ready thm, RightImpE pf1 ctx)
seekUp (pf2, RightImpE pf1 ctx) = case (pf1, pf2) of 
                                    (Ready _, Ready _) -> collapseToTheorem (ImpE pf1 pf2) >>= wrap ctx
                                    _                  -> seekUp (ImpE pf1 pf2, ctx)
seekUp (pf, DownSpikeE phi ctx) = caseDown pf ctx (SpikeE phi)
seekUp (pf, DownQUI s ctx) = caseDown pf ctx (QUI s)
seekUp (pf, DownQUE t ctx) = caseDown pf ctx (QUE t)
seekUp (pf1, LeftAndI ctx pf2) = case seekDown (pf2, RightAndI pf1 ctx) of 
                                  Just loc -> Right loc 
                                  Nothing  -> collapseToTheorem pf2 >>= \thm -> seekUp (Ready thm, RightAndI pf1 ctx)
seekUp (pf2, RightAndI pf1 ctx) = case (pf1, pf2) of 
                                    (Ready _, Ready _) -> collapseToTheorem (AndI pf1 pf2) >>= wrap ctx 
                                    _ -> seekUp (AndI pf1 pf2, ctx)
seekUp (pf, DownAndE1 ctx) = caseDown pf ctx AndE1 
seekUp (pf, DownAndE2 ctx) = caseDown pf ctx AndE2 
seekUp (pf, DownOrI1 phi ctx) = caseDown pf ctx (OrI1 phi)
seekUp (pf, DownOrI2 phi ctx) = caseDown pf ctx (OrI2 phi)
seekUp (pf1, LeftOrE ctx pf2 pf3) = case seekDown (pf2, MiddleOrE pf1 ctx pf3) of 
                                      Just loc -> Right loc 
                                      Nothing  -> collapseToTheorem pf2 >>= \thm -> seekUp (Ready thm, MiddleOrE pf1 ctx pf3)
seekUp (pf2, MiddleOrE pf1 ctx pf3) = case seekDown (pf3, RightOrE pf1 pf2 ctx) of
                                        Just loc -> Right loc 
                                        Nothing  -> seekUp (pf3, RightOrE pf1 pf2 ctx)
seekUp (pf3, RightOrE pf1 pf2 ctx) = case (pf1, pf2, pf3) of 
                                      (Ready _, Ready _, Ready _) -> collapseToTheorem (OrE pf1 pf2 pf3) >>= wrap ctx 
                                      _                           -> seekUp (OrE pf1 pf2 pf3, ctx)
seekUp (pf, DownQEI phi s t ctx) = caseDown pf ctx (QEI phi s t)
seekUp (pf1, LeftQEE ctx pf2) = case seekDown (pf2, RightQEE pf1 ctx) of 
                                  Just loc -> Right loc 
                                  Nothing  -> collapseToTheorem pf2 >>= \thm -> seekUp (Ready thm, RightQEE pf1 ctx)
seekUp (pf2, RightQEE pf1 ctx) = case (pf1, pf2) of 
                                  (Ready _, Ready _) -> collapseToTheorem (QEE pf1 pf2) >>= wrap ctx 
                                  _                  -> seekUp (QEE pf1 pf2, ctx)
seekUp (pf, DownEquiv phi ctx) = caseDown pf ctx (Equiv phi)

next :: Location -> Either String Location 
next loc@(_, Root) = case seekDown loc of 
                      Just loc' -> Right loc' 
                      Nothing   -> Left "next: no more goals"
next loc = case seekUp loc of 
            Right (pf, Root) -> next (pf, Root)
            res              -> res 

--- konstruowanie drzewa dowodu
--  Niezmiennik: funkcja zwraca lokalizację jakiegoś celu wtedy i tylko wtedy,
--               gdy w dowodzie po zastosowaniu reguły istnieje cel. 
introImp :: String -> Location -> Either String Location 
introImp s (Goal gamma (Binop phi Imp psi), ctx) = Right (Goal (List.union gamma [(s, phi)]) psi, DownImpI phi ctx)
introImp _ _ = Left "introImp: no implication to introduce"

introForall ::  Location -> Either String Location 
introForall (Goal gamma (QU x phi), ctx) 
  | not (any (freeInFormula x . snd) gamma) = Right (Goal gamma phi, DownQUI x ctx)
  | otherwise = Left "introForall: bad choice of name for fresh variable"
introForall _ = Left "introForall: no universal quantifier to introduce"

{-  Γ ⊢ ∀x φ      Znów „cofamy podstawienie”. 
 -------------∀e  Użytkownik mając φ' podaje nazwę zmiennej x, term t oraz formułę φ,
     Γ ⊢ φ'       takie że φ[x/t] = φ'. -}
elimForall :: Location -> String -> Term -> Formula -> Either String Location 
elimForall (Goal gamma phi', ctx) s t phi = case substInFormula phi s t of 
                                              Just psi -> if psi == phi' 
                                                            then Right (Goal gamma (QU s phi), DownQUE t ctx) 
                                                            else Left "elimForall: bad formula or term"
                                              Nothing  -> Left "elimForall: inadmissible substitution"

elimImp :: Location -> Formula -> Either String Location 
elimImp (Goal gamma psi, ctx) phi = Right (Goal gamma (Binop phi Imp psi), LeftImpE ctx (Goal gamma phi))
elimImp _ _ = Left "elimImp: not at goal"

elimSpike :: Location -> Either String Location 
elimSpike (Goal gamma phi, ctx) = Right (Goal gamma Spike, DownSpikeE phi ctx)
elimSpike _  = Left "elimSpike: not at goal"

readyByAssumption :: Location -> String -> Either String Location 
readyByAssumption (Goal gamma phi, ctx) ass = case lookup ass gamma of 
                                                Just psi -> if psi == phi 
                                                              then let thm = byAssumption psi in 
                                                                case next (Ready thm, ctx) of 
                                                                      Left "next: no more goals" -> Right (Ready thm, ctx)
                                                                      res -> res
                                                              else Left "readyByAssumption: wrong assumption for this goal"
                                                Nothing  -> Left "readyByAssumption: no such assumption"
readyByAssumption _ _ = Left "readyByAssumption: not at goal"

readyByTheorem :: Location -> Theorem -> Either String Location 
readyByTheorem (Goal gamma psi, ctx) thm = if all (`elem` map snd gamma) (assumptions thm) && consequence thm == psi
                                            then next (Ready thm, ctx)
                                            else Left "readyByTheorem: wrong theorem for this goal"
readyByTheorem _ _ = Left "readyByTheorem: not at goal"

introAnd :: Location -> Either String Location 
introAnd (Goal gamma (Binop phi And psi), ctx) = Right (Goal gamma phi, LeftAndI ctx (Goal gamma psi))
introAnd _ = Left "introAnd: no conjunction to introduce"

introOr :: Location -> Bool -> Either String Location 
introOr (Goal gamma (Binop phi Or psi), ctx) left = Right $ if left 
                                                              then (Goal gamma phi, DownOrI1 psi ctx)
                                                              else (Goal gamma psi, DownOrI2 phi ctx)
introOr _ _ = Left "introOr: no disjunction to introduce"

introExists :: Location -> Term -> Either String Location 
introExists (Goal gamma (QE x phi), ctx) t = case substInFormula phi x t of 
                                               Just phi' -> Right (Goal gamma phi', DownQEI phi x t ctx)
                                               Nothing   -> Left "introExists: inadmissible substitution"
introExists _ _ = Left "introExists: no existential quantifier to introduce"

elimAnd :: Location -> Formula -> Bool -> Either String Location
elimAnd (Goal gamma phi, ctx) psi left = Right $ if left 
                                                  then (Goal gamma (Binop phi And psi), DownAndE1 ctx)
                                                  else (Goal gamma (Binop psi And phi), DownAndE2 ctx)
elimAnd _ _ _ = Left "elimAnd: not at goal"

elimOr :: Location -> Formula -> String -> Formula -> String -> Either String Location
elimOr (Goal gamma phi, ctx) psi psiName lambda lambdaName = Right (Goal gamma (Binop psi Or lambda), 
                                                                    LeftOrE ctx 
                                                                            (Goal (List.union gamma [(psiName, psi)]) phi)
                                                                            (Goal (List.union gamma [(lambdaName, lambda)]) phi))
elimOr _ _ _ _ _ = Left "elimOr: not at goal"

elimExists :: Location -> Formula -> String -> String -> Either String Location 
elimExists (Goal gamma phi, ctx) psi x psiName = Right (Goal gamma (QE x psi), 
                                                        LeftQEE ctx
                                                                (Goal (List.union gamma [(psiName, psi)]) phi))
elimExists _ _ _ _ = Left "elimExists: not at goal"

equivRule :: Location -> Formula -> Either String Location 
equivRule (Goal gamma phi, ctx) psi = Right (Goal gamma psi, DownEquiv phi ctx)
equivRule _ _ = Left "equivRule: not at goal"

isGoal :: Proof -> Bool 
isGoal (Goal _ _) = True 
isGoal _ = False 

uncons :: Location -> Location
uncons (Goal gamma phi, DownImpI psi ctx) = (Goal (List.filter ((/= psi) . snd) gamma) (Binop phi Imp psi), ctx)

uncons (Goal gamma phi, LeftImpE ctx pf2) = uncons (ImpE (Goal gamma phi) pf2, ctx)
uncons (Goal gamma phi, RightImpE pf1 ctx) = uncons (ImpE pf1 (Goal gamma phi), ctx)
uncons (ImpE (Goal gamma (Binop phi Imp psi)) (Goal _ _), ctx) = (Goal gamma psi, ctx)

uncons (Goal gamma _, DownSpikeE psi ctx) = (Goal gamma psi, ctx)
uncons (Goal gamma phi, DownQUI s ctx) = (Goal gamma (QU s phi), ctx)
uncons (Goal gamma (QU x phi), DownQUE t ctx) = case substInFormula phi x t of 
                                                  Just phi' -> (Goal gamma phi', ctx)
                                                  Nothing   -> undefined -- niemożliwe

uncons (Goal gamma phi, LeftAndI ctx pf2) = uncons (AndI (Goal gamma phi) pf2, ctx)
uncons (Goal gamma phi, RightAndI pf1 ctx) = uncons (AndI pf1 (Goal gamma phi), ctx)
uncons (AndI (Goal gamma phi) (Goal _ psi), ctx) = (Goal gamma (Binop phi And psi), ctx)

uncons (Goal gamma (Binop phi And _), DownAndE1 ctx) = (Goal gamma phi, ctx)
uncons (Goal gamma (Binop _ And psi), DownAndE2 ctx) = (Goal gamma psi, ctx)

uncons (Goal gamma phi, DownOrI1 psi ctx) = (Goal gamma (Binop phi Or psi), ctx)
uncons (Goal gamma psi, DownOrI2 phi ctx) = (Goal gamma (Binop phi Or psi), ctx)

uncons (Goal gamma phi, LeftOrE ctx pf2 pf3) = uncons (OrE (Goal gamma phi) pf2 pf3, ctx)
uncons (Goal gamma phi, MiddleOrE pf1 ctx pf3) = uncons (OrE pf1 (Goal gamma phi) pf3, ctx)
uncons (Goal gamma phi, RightOrE pf1 pf2 ctx) = uncons (OrE pf1 pf2 (Goal gamma phi), ctx)
uncons (OrE (Goal gamma _) (Goal _ lambda) (Goal _ _), ctx) = (Goal gamma lambda, ctx)

uncons (Goal gamma phi', DownQEI phi s _ ctx) = (Goal gamma (QE s phi), ctx)

uncons (pf1, LeftQEE ctx pf2) = uncons (QEE pf1 pf2, ctx)
uncons (pf2, RightQEE pf1 ctx) = uncons (QEE pf1 pf2, ctx)
uncons (QEE (Goal gamma (QE x phi)) (Goal delta psi), ctx) = (Goal gamma psi, ctx)

uncons (Goal gamma _, DownEquiv phi ctx) = (Goal gamma phi, ctx)
uncons loc
  | not $ isGoal (fst loc) = case seekDown loc of 
                            Just loc' -> uncons loc' 
                            Nothing   -> loc 
  | otherwise = undefined 
