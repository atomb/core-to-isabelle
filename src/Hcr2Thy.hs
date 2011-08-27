module Main where

import System.Environment
import System.FilePath ( takeBaseName )
import Text.PrettyPrint.Leijen.Text ( putDoc )

import Language.Core.Parser
import Language.Core.ParseGlue
import Language.Core.Isabelle

main :: IO ()
main = do
  [f] <- getArgs
  c   <- readFile f
  let newName = takeBaseName f
  case parse c 0 of
    FailP s -> putStrLn $ "Failed: " ++ s
    OkP m   -> putDoc $ processModule m newName
