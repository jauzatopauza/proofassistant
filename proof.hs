module Proof where 
import Logic

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
    | QEE String Proof Proof -- udowadniamy, że coś istnieje, nazywamy to i korzystamy z tego w innym dowodzie
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
    | LeftQEE String Path Proof 
    | RightQEE String Proof Path 
    | DownRBV String Path 

type Location = (Proof, Path)

proof :: Assumptions -> Formula -> Location 
proof gamma phi = (Goal gamma phi, Root)
