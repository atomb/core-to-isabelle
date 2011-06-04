module Main where

import System.Environment
import System.FilePath ( takeBaseName )
import qualified Data.ByteString.Lazy.Char8 as L

import Language.Core.Parser
import Language.Core.Isabelle

main :: IO ()
main = do
  [f] <- getArgs
  c   <- L.readFile f
  let newName = takeBaseName f
  case parseModule newName c of
    Left err -> putStrLn $ "Failed: " ++ show err
    Right  m -> putStrLn $ processModule m newName
