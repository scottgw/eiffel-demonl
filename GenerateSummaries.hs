{-# LANGUAGE ScopedTypeVariables #-}
module GenerateSummaries where

import Data.Either
import Data.Map (Map)

import Language.Eiffel.Syntax
import Language.Eiffel.Parser.Parser
import Language.Eiffel.Summary
import Language.Eiffel.Util

import System.Directory
import System.FilePath
import System.FilePath.Find

homeDir :: [String]
homeDir = ["/","home","scott"]

srcDir :: [String]
srcDir = homeDir ++ ["src"]

localDir :: [String]
localDir = homeDir ++ ["local"]

libraryDir :: [String]
libraryDir = localDir ++ ["Eiffel70","library"]

libraryNames :: [String]
libraryNames = ["base2","base","thread","test"]

searchDirectories :: [(String, FilePath)]
searchDirectories = zip libraryNames $
  map joinPath 
    [ srcDir ++ ["eiffelbase2","trunk"]
    , libraryDir ++ ["base","elks"]
    , libraryDir ++ ["thread","classic"]
    , srcDir ++ ["eiffel-demonl"]
    ]

-- | Search the argument directories for all Eiffel files.
searchEiffelFiles :: FilePath -> IO [FilePath]
searchEiffelFiles dir = findExt dir ".e"
 
searchSummaries :: FilePath -> IO [FilePath]
searchSummaries dir = findExt dir ifaceExt

ifaceExt :: String
ifaceExt = ".ebi"

findExt :: FilePath -> FilePath -> IO [FilePath]
findExt dir ext = find (return True) (extension ==? ext) dir
                        
genSummary :: String -> [FilePath] -> IO ()
genSummary name pathes = do
  classesEi <- mapM ( \path -> print path >> parseClassFile path) pathes
  let classes = rights classesEi
      errs = lefts classesEi
      interfaces = map clasInterface classes
  print errs
  pwd <- getCurrentDirectory
  writeBinarySummary (pwd </> name ++ ifaceExt) interfaces

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
