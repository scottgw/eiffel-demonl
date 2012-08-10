module Test where

import Data.Char

import Language.DemonL.PrettyPrint

import qualified Language.Eiffel.PrettyPrint as PP
import Language.Eiffel.TypeCheck.TypedExpr as T

import System.FilePath
import System.Environment

import ClassEnv
import DomainGen
import InstrumentClass
import Driver

main :: IO ()
main = do
  class_ : routine : _ <- getArgs
  
  let
    classLower = map toLower class_
    classFile  = classLower <.> "e"
    instrumentedFile = classLower ++ "_instr" <.> "e"
  
  -- produce headers (unconditionally for now)
  regenHeader class_  classFile

  -- instrument class  
  (typedDependencies, typedClass) <- loadDepsAndClass classFile
  let flatEnv = flattenEnv $ makeEnv typedDependencies
  writeFile instrumentedFile 
    (show $ PP.toDoc $ untype $ instrument flatEnv routine typedClass)
  
  let (dom, extraInstrClass) = domain routine typedClass flatEnv  
  -- generate minimal domain
  writeFile (class_ <.> "dmn") (show $ domainDoc untypeExprDoc dom)
  
  -- generate extra serializaiton class
  writeFile "extra_instr.e" (show $ PP.toDoc extraInstrClass)