module Main where

import System.Environment

import GHC
import Outputable
import DynFlags ( defaultDynFlags )
import GHC.Paths ( libdir )


processModule :: String -> IO ()
processModule filename =
  defaultErrorHandler defaultDynFlags $ do
    coreMod <- runGhc (Just libdir) $ do
      dflags <- getSessionDynFlags
      setSessionDynFlags dflags
      compileToCoreModule filename
    putStrLn . showSDoc . ppr $ coreMod

main :: IO ()
main = getArgs >>= mapM_ processModule
