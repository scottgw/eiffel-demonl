module Main where

import Control.Exception

import Language.Eiffel.Parser.Parser
import Language.Eiffel.Eiffel

import Language.Eiffel.TypeCheck.Class

import System.Directory
import System.FilePath

import DepGen

src = ["/","home","scott","src"]
local = ["/","home","scott","local"]

searchDirectories = 
  map joinPath 
    [ src ++ ["eiffelbase2","trunk"]
    , local ++ ["Eiffel70","library","base","elks"]
    ]

main = do
  currDir <- getCurrentDirectory
  let testDir = currDir </> "test"
  print searchDirectories
  files <- collectFileMap (testDir : searchDirectories)
  print files
  classEi <- parseClassFile (testDir </> "work_queue.e")
  case classEi of
    Left e -> putStrLn (show e)
    Right cls -> do
      classInterfacesEi <- depGenInt files (className cls)
      putStrLn "Generated dependencies"
      case classInterfacesEi of
        Left e -> putStrLn (show e) 
        Right classInts -> 
          case clasM classInts cls of
            Left e -> print e
            Right typedClass -> putStrLn "Typecheck successful"
