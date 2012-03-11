{-# LANGUAGE ScopedTypeVariables #-}

module GenerateSummaries where

import Data.Either
import qualified Data.Map as Map
import Data.Map (Map)

import Language.Eiffel.Syntax
import Language.Eiffel.Parser.Parser
import Language.Eiffel.Summary
import Language.Eiffel.Util

import System.Directory
import System.FilePath
import System.FilePath.Find

home = ["/","home","scott"]
src = home ++ ["src"]
local = home ++ ["local"]
library = local ++ ["Eiffel70","library"]

names = ["base2","base","thread","test"]

searchDirectories = zip names  $
  map joinPath 
    [ src ++ ["eiffelbase2","trunk"]
    , library ++ ["base","elks"]
    , library ++ ["thread","classic"]
    , src ++ ["eiffel-demonl"]
    ]

-- | Search the argument directories for all Eiffel files.
searchEiffelFiles :: FilePath -> IO [FilePath]
searchEiffelFiles dir = findExt dir ".e"
 
searchSummaries dir = findExt dir ext

ext = ".ebi"

findExt dir ext = find (return True) (extension ==? ext) dir
                        
genSummary :: String -> [FilePath] -> IO ()
genSummary name pathes = do
  classesEi <- mapM ( \path -> print path >> parseClassFile path) pathes
  let classes = rights classesEi
      errs = lefts classesEi
      interfaces = map clasInterface classes
  print errs
  pwd <- getCurrentDirectory
  writeBinarySummary (pwd </> name ++ ext) interfaces

genAllSummaries :: IO ()
genAllSummaries =
  mapM_ (\ (name, dir) -> do
            files <- searchEiffelFiles dir
            genSummary name files) searchDirectories
  
readAllSummaries :: IO (Map ClassName ClasInterface)
readAllSummaries = do
  pwd <- getCurrentDirectory
  summaryFiles <- searchSummaries pwd
  summaries <- mapM readBinarySummary summaryFiles
  -- let interfaces :: [[ClasInterface]] = rights summariesEi
  -- putStrLn (show $ lefts $ summariesEi)
  return $ clasMap $ concat summaries
