{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}

module Gui where 

import Data.GI.Base 
import qualified GI.Gtk as Gtk 
import Logic
import Proof ( Path(Root), Proof(Goal), readyByTheorem, Location, goal, collapseToTheorem, Assumptions )
import Control.Concurrent.MVar
import GI.Gdk (keyvalName, getEventKeyKeyval, getEventKeyState)
import qualified Data.Text as Text
import Parser

writeError :: String -> Gtk.TextView -> IO ()
writeError err = writeToView ("Error. " <> err) 

writeToView :: String -> Gtk.TextView -> IO ()
writeToView s view = do  buf <- get view #buffer 
                         ins <- Gtk.textBufferGetInsert buf
                         it <- Gtk.textBufferGetIterAtMark buf ins 
                         Gtk.textBufferInsert buf it (Text.pack s <> "\n") (-1)

tryAxiom :: (Location, String) -> MVar (Location, String) -> Theorem -> Gtk.TextView -> IO ()
tryAxiom (loc, s) lc thm errView = case readyByTheorem loc thm of 
                        Left err -> do  putMVar lc (loc, s)
                                        writeError err errView
                        Right loc' -> do putMVar lc (loc', s) 
 
assmInfo :: Assumptions -> String 
assmInfo = foldl (\acc (s, phi) -> acc ++ s ++ ": " ++ show phi ++ "\n") ""

runAssistant :: Theory t => (String -> Either String t) -> IO ()
runAssistant parseAxiom
     = do Gtk.init Nothing 
          win <- new Gtk.Window [#title := "Proof Assistant"]
          on win #destroy Gtk.mainQuit
          #resize win 1000 650
          
          outerBox <- new Gtk.Box [#orientation := Gtk.OrientationHorizontal]
          #add win outerBox 

          innerLeftBox <- new Gtk.Box [#orientation := Gtk.OrientationVertical]
          #packStart outerBox innerLeftBox True True 5

          scrWinRepl <- new Gtk.ScrolledWindow []
          txtRepl <- new Gtk.TextView []
          #packStart innerLeftBox scrWinRepl True True 10

          set scrWinRepl [#child := txtRepl]
          entry <- new Gtk.Entry []
          #packStart innerLeftBox entry True False 10 
          
          innerRightBox <- new Gtk.Box [#orientation := Gtk.OrientationVertical]
          #packStart outerBox innerRightBox True True 5

          scrWinAssm <- new Gtk.ScrolledWindow []
          scrWinGoal <- new Gtk.ScrolledWindow []
          labelAssm <- new Gtk.Label [#label := "Assumptions: "]
          labelGoal <- new Gtk.Label [#label := "Goal: "]
          
          #packStart innerRightBox labelAssm False False 5
          #packStart innerRightBox scrWinAssm True True 10
          #packStart innerRightBox labelGoal False False 5
          #packStart innerRightBox scrWinGoal True True 10
          txtAssm <- new Gtk.TextView []
          set scrWinAssm [#child := txtAssm]
          txtGoal <- new Gtk.TextView []
          set scrWinGoal [#child := txtGoal]
          mapM_ (flip set [#editable := False, #cursorVisible := False, #wrapMode := Gtk.WrapModeChar]) [txtRepl, txtAssm, txtGoal]

          lc <- newMVar ((Goal [] Spike, Root), "init") -- lokalizacja w dowodzie i nazwa dowodzonego twierdzenia
          takeMVar lc 
          thms <- newMVar ([] :: [(String, Theorem)])

          Gtk.onWidgetKeyPressEvent entry $ \e -> 
            getEventKeyState e >>= \res -> 
                case res of 
                    [] -> getEventKeyKeyval e >>= keyvalName >>= \s -> 
                            case s of 
                                Just "Return" -> do buf <- get txtRepl #buffer 
                                                    ins <- Gtk.textBufferGetInsert buf
                                                    it <- Gtk.textBufferGetIterAtMark buf ins 
                                                    txt1 <- get entry #text 
                                                    set entry [#text := ""]
                                                    Gtk.textBufferInsert buf it (txt1 <> "\n") (-1)
                                                    
                                                    let txt = Text.unpack txt1 
                                                    mlc <- tryTakeMVar lc 
                                                    thms' <- readMVar thms
                                                    
                                                    case mlc of 
                                                       Just (loc, s) -> case parseCommand thms' loc txt of 
                                                                           Right loc' -> putMVar lc (loc', s) 
                                                                           Left "ABANDONED" -> return ()
                                                                           Left err -> case parseAxiom txt of 
                                                                                        Right thm -> tryAxiom (loc, s) lc (ax thm) txtRepl
                                                                                        Left _ -> do   putMVar lc (loc, s) 
                                                                                                       writeError err txtRepl 
                                                       Nothing -> case parseInitCommand txt of 
                                                                      Right loc -> putMVar lc loc 
                                                                      Left err -> writeError err txtRepl 
                                                    
                                                    mlc <- tryTakeMVar lc 
                                                    assmBuf <- get txtAssm #buffer 
                                                    goalBuf <- get txtGoal #buffer 
                                                    case mlc of 
                                                        Just ((pf, ctx), s) -> case goal pf of 
                                                                                Nothing -> do writeToView ("Proven " ++ s) txtRepl 
                                                                                              set assmBuf [#text := ""]
                                                                                              set goalBuf [#text := ""]
                                                                                              thms2 <- takeMVar thms 
                                                                                              case collapseToTheorem pf of 
                                                                                                Right thm -> putMVar thms ((s, thm):thms2)
                                                                                                Left err ->  do writeError err txtRepl 
                                                                                                                putMVar thms thms2
                                                                                Just (assms, phi) -> do set assmBuf [#text := Text.pack $ assmInfo assms]
                                                                                                        set goalBuf [#text := Text.pack $ show phi ++ "\n(Proving " ++ s ++ ")"]
                                                                                                        putMVar lc ((pf, ctx), s)
                                                        Nothing -> do set assmBuf [#text := ""]
                                                                      set goalBuf [#text := ""]
                                                                                              
                                                    return True 
                                _ -> return False 
                    _ -> return False

          #showAll win
          Gtk.main  