{-# LANGUAGE ScopedTypeVariables #-}

module GenerateSummaries where

import Data.Char
import Data.Either
import qualified Data.Map as Map
import Data.Map (Map)

import Language.Eiffel.Eiffel
import Language.Eiffel.Parser.Parser
import Language.Eiffel.Summary

import Text.Parsec.Error
import Text.Parsec.Pos

import System.Directory
import System.FilePath
import System.FilePath.Find


src = ["/","home","scott","src"]
local = ["/","home","scott","local"]
library = local ++ ["Eiffel70","library"]

names = ["base2","base","thread"]

searchDirectories = zip names  $
  map joinPath 
    [ src ++ ["eiffelbase2","trunk"]
    , library ++ ["base","elks"]
    , library ++ ["thread","classic"]
    ]

-- | Search the argument directories for all Eiffel files.
searchEiffelFiles :: FilePath -> IO [FilePath]
searchEiffelFiles dir = findExt dir ".e"
 
searchSummaries dir = findExt dir ".eis"                        

findExt dir ext = find (return True) (extension ==? ext) dir
                        
genSummary :: String -> [FilePath] -> IO ()
genSummary name pathes = do
  classesEi <- mapM ( \path -> print path >> parseClassFile path) pathes
  let classes = rights classesEi
      errs = lefts classesEi
      interfaces = map clasInterface classes
  print errs
  pwd <- getCurrentDirectory
  writeSummary (pwd </> name ++ ".eis") interfaces

genAllSummaries :: IO ()
genAllSummaries =
  mapM_ (\ (name, dir) -> do
            files <- searchEiffelFiles dir
            genSummary name files) searchDirectories
  
readAllSummaries :: IO (Map ClassName ClasInterface)
readAllSummaries = do
  pwd <- getCurrentDirectory
  summaryFiles <- searchSummaries pwd
  summariesEi <- mapM parseSummary summaryFiles
  let interfaces :: [[ClasInterface]] = rights summariesEi
  putStrLn (show $ lefts $ summariesEi)
  return $ clasMap $ concat interfaces

newtype ClassMap = ClassMap (Map String FilePath) deriving Show

fromList = ClassMap . Map.fromList

lookupName "string" cMap     = lookupName "string_8" cMap
lookupName "character" cMap  = lookupName "character_8" cMap
lookupName "double" cMap     = lookupName "real_64" cMap
lookupName "natural" cMap    = lookupName "natural_32" cMap
lookupName name (ClassMap m) = Map.lookup name m

classNameFileMap :: [FilePath] -> ClassMap
classNameFileMap = 
  let fileAndPath file = (takeBaseName file, file)
  in fromList . map fileAndPath