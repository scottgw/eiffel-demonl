module DepGen (collectFileMap, depGen, depGenInt) where

import Control.Monad
import Control.Monad.Error
import Control.Monad.Reader

import Data.Char
import qualified Data.Map as Map
import Data.Map (Map)

import Language.Eiffel.Eiffel
import Language.Eiffel.Parser.Parser

import Text.Parsec.Error
import Text.Parsec.Pos

import System.FilePath
import System.FilePath.Find


-- | Search the argument directories for all Eiffel files.
collectEiffelFiles :: [FilePath] -> IO [FilePath]
collectEiffelFiles dirs = do
  pathLists <- mapM (find (return True) (extension ==? ".e")) dirs
  return (concat pathLists)

newtype ClassMap = ClassMap (Map String FilePath) deriving Show

fromList = ClassMap . Map.fromList


lookupName "string" cMap     = lookupName "string_8" cMap
lookupName name (ClassMap m) = Map.lookup name m

classNameFileMap :: [FilePath] -> ClassMap
classNameFileMap = 
  let fileAndPath file = (takeBaseName file, file)
  in fromList . map fileAndPath

collectFileMap :: [FilePath] -> IO ClassMap
collectFileMap dirs = classNameFileMap `fmap` collectEiffelFiles dirs

type DepM = ErrorT ParseError (ReaderT ClassMap IO)

instance Error ParseError where
    strMsg s = newErrorMessage (Message s) (initialPos "NoFile") 

depGen :: ClassMap -> ClassName -> IO (Either ParseError [Clas])
depGen classMap = flip runReaderT classMap . runErrorT . flip depGen' []

depGenInt :: ClassMap -> ClassName -> IO (Either ParseError [ClasInterface])
depGenInt classMap = fmap (fmap (map clasInterface)) . depGen classMap

depGen' :: ClassName -> [Clas] -> DepM [Clas]
depGen' cn acc = do
  classMap <- ask
  let fileNameMb = lookupName (map toLower cn) classMap
  newClass <- case fileNameMb of
    Nothing -> throwError (strMsg $ "couldn't find file for " ++ cn)
    Just fileName -> do
      lift (lift $ putStrLn fileName)
      newClassEi <- lift (lift $ parseClassFile fileName)
      either throwError return newClassEi
--  writeInterface (extractInterface newClass)
  depClas newClass (newClass:acc)

depClas :: Clas -> [Clas] -> DepM [Clas]
depClas c acc = 
    depRoutines c (acc ++ genericStubs c) >>= depAttrs c >>= depInherit c

depInherit :: Clas -> [Clas] -> DepM [Clas]
depInherit c acc = foldM depTyp acc (map inheritClass $ inherit c)

depRoutines :: Clas -> [Clas] -> DepM [Clas]
depRoutines c acc = foldM depRoutine acc (allRoutines c)

depAttrs :: Clas -> [Clas] -> DepM [Clas]
depAttrs c acc = depDecls (map attrDecl $ allAttributes c) acc

depRoutine :: [Clas] -> Routine -> DepM [Clas]
depRoutine acc f = 
    let fSig     = Decl (featureName f) (featureResult f)
        locals   = 
          case routineImpl f of
            RoutineDefer -> []
            body -> routineLocal body
        allDecls = fSig : locals ++ routineArgs f
    in depDecls allDecls acc

depDecls :: [Decl] -> [Clas] -> DepM [Clas]
depDecls ds acc = foldM depDecl acc ds

hasClas :: ClassName -> [Clas] -> Bool
hasClas cn = any ( (==) cn . className)

depDecl :: [Clas] -> Decl -> DepM [Clas]
depDecl acc (Decl _ t) = depTyp acc t

depTyp :: [Clas] -> Typ -> DepM [Clas]
depTyp acc (ClassType cn gs)
    | not (hasClas cn acc) = foldM depTyp acc gs >>= depGen' cn
    | otherwise = return acc
depTyp acc (Sep _ _ cn) = depTyp acc (ClassType cn [])
depTyp acc _ = return acc
