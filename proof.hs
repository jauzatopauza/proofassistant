module Proof where 
import Logic
import Control.Applicative ( Alternative((<|>)) )

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
    | QEE Proof Proof -- udowadniamy, że coś istnieje, i korzystamy z tego w innym dowodzie; może być potrzebne skorzystanie z RBV
    | RBV String Proof   -- dowód formuły z kwantyfikatorem i nowa nazwa zmiennej związanej

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
    | DownRBV String Path 

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
goal (RBV _ pf) = goal pf 
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
collapseToTheorem (RBV s pf) = collapseToTheorem pf >>= flip rbv s 

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
seekDown (RBV s pf, ctx) = seekDown (pf, DownRBV s ctx)

{--------------------- ŹLE ------------------------------------
-- funkcja do wychodzenia
caseDown :: Location -> (Proof -> Location) -> Either String Location 
caseDown loc cont = case seekDown loc of 
                      Just loc' -> seekUp $ cont $ fst loc 
                      Nothing -> collapseToTheorem (fst loc) >>= \thm -> seekUp $ cont (Ready thm) 

seekUp :: Location -> Either String Location 
seekUp l@(pf, Root) = case seekDown l of 
                        Just loc' -> Right loc' 
                        Nothing -> collapseToTheorem pf >>= \thm -> return (Ready thm, Root)
seekUp l@(_, DownImpI phi ctx) = caseDown l $ \pf -> (ImpI phi pf, ctx)
seekUp (pf1, LeftImpE ctx pf2) = case seekDown loc of 
                                    Just loc' -> Right loc' 
                                    Nothing -> seekUp loc 
                                   where loc = (pf2, RightImpE pf1 ctx)
seekUp l@(_, RightImpE pf1 ctx) = caseDown l $ \pf2 -> (ImpE pf1 pf2, ctx)
-}
