{-# LANGUAGE OverloadedStrings #-}
module Test where

import           Data.Char
import qualified Data.HashMap.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import           Data.Text (Text)

import           Language.DemonL.PrettyPrint
import qualified Language.Eiffel.PrettyPrint as PP
import           Language.Eiffel.TypeCheck.TypedExpr as T

import           System.FilePath
import           System.Environment

import           ClassEnv
import           DomainGen
import           InstrumentClass
import           SerialGen
import           Driver (regenHeaderHere, regenHeader, flattenEnv, loadDepsAndClass)


main :: IO ()
main = do
  class_ : routine : _ <- fmap (map Text.pack) getArgs
  instrumentClass class_ routine

instrumentClass :: Text -> Text -> IO ()
instrumentClass class_ routine = do
  let
    classLower = Text.unpack $ Text.toLower class_
    classFile  = classLower <.> "e"
    instrumentedFile = classLower ++ "_instr" <.> "e"

  -- -- produce headers (unconditionally for now)
  -- putStrLn "Regenerate headers"
  -- regenHeader class_ classFile

  -- regenerate only the local headers (unconditionally for now)
  putStrLn "Regenerate local headers"
  regenHeaderHere class_ classFile    
  
  -- instrument class
  putStrLn "Load dependencies and class"
  (typedDependencies, typedClass) <- loadDepsAndClass classFile
  let flatEnv = flattenEnv $ makeEnv typedDependencies
  writeFile instrumentedFile 
    (show $ PP.toDoc $ untype $ instrument flatEnv routine typedClass)
  
  let (dom, featMap) = domain routine typedClass flatEnv
  -- generate minimal domain
  putStrLn "Writing domain"
  writeFile (Text.unpack class_ <.> "dmn") (show $ domainDoc typeExprDoc dom)
  
  -- generate the serialization class
  putStrLn "Generating serialization class"
  generateSerializer "serializer_template.e" "serializer.e" flatEnv (Map.map (Set.map Text.pack) featMap)