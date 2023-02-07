module Main where

import Gui
import Logic
import Data.Void

instance Theory Void where 
    axiom = absurd

main :: IO ()
main = runAssistant (const (Left "no axioms" :: Either String Void))
