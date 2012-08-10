module Main where

import qualified Language.Eiffel.PrettyPrint as PP

import Language.Eiffel.TypeCheck.TypedExpr as T

import System.Directory
import System.FilePath

import ClassEnv
import DomainGen
import InstrumentClass
import Driver

testClass = "work_queue"
testFeature = "dequeue"

testFile = testClass ++ ".e"

main :: IO ()
main = do
  currDir <- getCurrentDirectory
  let testPath = currDir </> "test" </> testFile 
  (typedDomain, typedClass) <- loadDepsAndClass testPath
  putStrLn "Typed"
  let flatEnv = flattenEnv $ makeEnv typedDomain
  print (PP.toDoc $ untype $ instrument flatEnv testFeature typedClass)
  domain testFeature typedClass flatEnv