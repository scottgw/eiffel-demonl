module DepGen (depGen) where

import Control.Monad
import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.Reader

import Data.Char
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)

import Language.Eiffel.Syntax
import Language.Eiffel.Position
import Language.Eiffel.Util
import Language.Eiffel.Parser.Parser

import Text.Parsec.Error
import Text.Parsec.Pos

import System.FilePath
import System.FilePath.Find

import ClassEnv

type DepM = ErrorT ParseError (ReaderT InterEnv Identity)

instance Error ParseError where
    strMsg s = newErrorMessage (Message s) (initialPos "NoFile") 

depGen :: InterEnv -> ClassName -> Either ParseError [ClasInterface]
depGen classMap name = 
  let dependencies = depGen' name []
  in runIdentity (runReaderT (runErrorT dependencies) classMap)

depGen' :: ClassName -> [ClasInterface] -> DepM [ClasInterface]
depGen' cn acc = do
  classMap <- ask
  let classMb = envLookup (map toLower cn) classMap
  newClass <- case classMb of
    Nothing -> throwError (strMsg $ "couldn't find file for " ++ cn)
    Just clas -> return clas
  depClas newClass (newClass:acc)

depClas :: ClasInterface -> [ClasInterface] -> DepM [ClasInterface]
depClas c acc = 
    depFeatures c (acc ++ genericStubs c) >>= depAttrs c >>= depInherit c

depInherit :: ClasInterface -> [ClasInterface] -> DepM [ClasInterface]
depInherit c acc = foldM depTyp acc (allInheritedTypes c)

depFeatures :: ClasInterface -> [ClasInterface] -> DepM [ClasInterface]
depFeatures c acc = foldM depFeature acc (allFeatures c)

depAttrs :: ClasInterface -> [ClasInterface] -> DepM [ClasInterface]
depAttrs c = depDecls (map attrDecl $ allAttributes c)

depFeature :: [ClasInterface] -> FeatureEx -> DepM [ClasInterface]
depFeature acc f = 
    let fSig     = Decl (featureName f) (featureResult f)
        allDecls = fSig : featureArgs f
    in depDecls allDecls acc

depDecls :: [Decl] -> [ClasInterface] -> DepM [ClasInterface]
depDecls ds acc = foldM depDecl acc ds

hasClas :: ClassName -> [ClasInterface] -> Bool
hasClas "DOUBLE"    = hasClas "REAL_64"
hasClas "CHARACTER" = hasClas "CHARACTER_8"
hasClas "STRING"    = hasClas "STRING_8"
hasClas cn = any ( (==) cn . className)

depDecl :: [ClasInterface] -> Decl -> DepM [ClasInterface]
depDecl acc (Decl _ t) = depTyp acc t

depTyp :: [ClasInterface] -> Typ -> DepM [ClasInterface]
depTyp acc (ClassType cn gs)
    | not (hasClas cn acc) = foldM depTyp acc gs >>= depGen' cn
    | otherwise = return acc
depTyp acc (Sep _ _ cn) = depTyp acc (ClassType cn [])
depTyp acc _ = return acc
