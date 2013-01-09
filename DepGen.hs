{-# LANGUAGE OverloadedStrings #-}

module DepGen (depGen) where

import           Control.Monad
import           Control.Monad.Error
import           Control.Monad.Identity
import           Control.Monad.Reader

import           Data.Char
import qualified Data.Text as Text
import           Data.Text (Text)

import           Language.Eiffel.Syntax
import           Language.Eiffel.Util

import           Text.Parsec.Error
import           Text.Parsec.Pos

import           ClassEnv

type DepM = ErrorT ParseError (ReaderT InterEnv Identity)

data ClassOrGeneric = Class ClasInterface | Gen ClasInterface

instance Error ParseError where
    strMsg s = newErrorMessage (Message s) (initialPos "NoFile") 

depGen :: InterEnv -> ClassName -> Either ParseError [ClasInterface]
depGen classMap name = 
  let dependencies = depGen' name []
      justClasses [] = []
      justClasses (Class c : cs) = c : justClasses cs
      justClasses (_ : cs) = justClasses cs
  in justClasses `fmap` 
     runIdentity (runReaderT (runErrorT dependencies) classMap)

depGen' :: ClassName -> [ClassOrGeneric] -> DepM [ClassOrGeneric]
depGen' cn acc = do
  classMap <- ask
  let classMb = envLookup (Text.toLower cn) classMap
  newClass <- case classMb of
    Nothing -> throwError (strMsg $ "couldn't find file for " ++ Text.unpack cn)
    Just clas -> return clas
  depClas newClass (Class newClass : acc)

-- make the generic stubs another type of interface,
-- so they can be filtered out at the end
-- this will require that the typechecking side-readd the generics for
-- each specific class
depClas :: ClasInterface -> [ClassOrGeneric] -> DepM [ClassOrGeneric]
depClas c acc = 
    depFeatures c (acc ++ map Gen (genericStubs c)) >>= 
    depAttrs c >>= depInherit c

depInherit :: ClasInterface -> [ClassOrGeneric] -> DepM [ClassOrGeneric]
depInherit c acc = foldM depTyp acc (allInheritedTypes c)

depFeatures :: ClasInterface -> [ClassOrGeneric] -> DepM [ClassOrGeneric]
depFeatures c acc = foldM depFeature acc (allFeatures c)

depAttrs :: ClasInterface -> [ClassOrGeneric] -> DepM [ClassOrGeneric]
depAttrs c = depDecls (map attrDecl $ allAttributes c)

depFeature :: [ClassOrGeneric] -> FeatureEx Expr -> DepM [ClassOrGeneric]
depFeature acc f = 
    let fSig     = Decl (featureName f) (featureResult f)
        allDecls = fSig : featureArgs f
    in depDecls allDecls acc

depDecls :: [Decl] -> [ClassOrGeneric] -> DepM [ClassOrGeneric]
depDecls ds acc = foldM depDecl acc ds

hasClas :: ClassName -> [ClassOrGeneric] -> Bool
hasClas "DOUBLE"    = hasClas "REAL_64"
hasClas "CHARACTER" = hasClas "CHARACTER_8"
hasClas "STRING"    = hasClas "STRING_8"
hasClas cName = 
  let clasGenName (Class c) = className c
      clasGenName (Gen gen) = className gen
  in any ((==) cName . clasGenName)

depDecl :: [ClassOrGeneric] -> Decl -> DepM [ClassOrGeneric]
depDecl acc (Decl _ t) = depTyp acc t

depTyp :: [ClassOrGeneric] -> Typ -> DepM [ClassOrGeneric]
depTyp acc (ClassType cn gs)
    | not (hasClas cn acc) = foldM depTyp acc gs >>= depGen' cn
    | otherwise = return acc
depTyp acc (TupleType _) = depTyp acc (ClassType "TUPLE" [])
depTyp acc (Sep _ _ cn) = depTyp acc (ClassType cn [])
depTyp acc _ = return acc
