module Main where

import Control.Exception

import Data.List
import qualified Data.Map as Map
import Data.Map (Map)

import Language.Eiffel.Parser.Parser
import Language.Eiffel.Eiffel
import qualified  Language.Eiffel.PrettyPrint as PP

import Language.Eiffel.TypeCheck.Class
import Language.Eiffel.TypeCheck.TypedExpr as T

import System.Directory
import System.FilePath

import DepGen

src = ["/","home","scott","src"]
local = ["/","home","scott","local"]
library = local ++ ["Eiffel70","library"]

searchDirectories = 
  map joinPath 
    [ src ++ ["eiffelbase2","trunk"]
    , library ++ ["base","elks"]
    , library ++ ["thread","classic"]
    ]

main = do
  currDir <- getCurrentDirectory
  let testDir = currDir </> "test"
  --  print searchDirectories
  files <- collectFileMap (testDir : searchDirectories)
  -- print files
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
            Right typedClass -> 
              putStrLn (show $ PP.toDoc $ untype $ 
                        instrument (clasMap classInts) "dequeue" typedClass)




instrument env routineName = 
  classMapRoutines (\r -> if featureName r == routineName
                          then instrumentRoutine env r
                          else r)

instrumentRoutine :: Env -> AbsRoutine RoutineBody TExpr 
                     -> AbsRoutine RoutineBody TExpr
instrumentRoutine env r = 
  r {routineImpl = instrumentBody env (routineEns r) (routineImpl r)}

instrumentBody :: Env -> Contract TExpr 
                  -> RoutineBody TExpr -> RoutineBody TExpr
instrumentBody env ens (RoutineBody locals localProc body) =
  let body' = snd $ stmt env (contractClauses ens) body
  in RoutineBody locals localProc body'
instrumentBody _ _ r = r

stmt :: Env -> [Clause TExpr] -> TStmt -> ([Clause TExpr], TStmt)
stmt env ens stmt = 
  let (cs, s) = stmt' env ens (contents stmt)
  in (cs, attachEmptyPos s)

p0 = attachEmptyPos

dummyExpr =
  let trg = p0 $ Var "mutex" (ClassType "MUTEX" []) 
      call = p0 $ Call trg "lock" [] NoType
      stmt = p0 $ CallStmt call
  in stmt
     
type Env = Map String ClasInterface

block (cs, s) = (cs, Block s)

replaceClause :: [Clause TExpr] -> TExpr -> TExpr -> [Clause TExpr]
replaceClause clauses old new = 
  map ( \cls -> 
         cls {clauseExpr = replaceExpr old new (clauseExpr cls)}) clauses

replaceExpr :: TExpr -> TExpr -> TExpr -> TExpr
replaceExpr new old = p0 . go . contents
  where 
    rep = replaceExpr new old
    go (T.Call trg name args t) = T.Call (rep trg) name (map rep args) t
    go (T.Access trg name t)    = T.Access (rep trg) name t
    go (T.BinOpExpr op e1 e2 t) = T.BinOpExpr op (rep e1) (rep e2) t
    go (T.UnOpExpr op e t)      = T.UnOpExpr op (rep e) t
    go (T.Attached mt e ms)     = T.Attached mt (rep e) ms
    go (T.Box t e)              = T.Box t (rep e)
    go (T.Unbox t e)            = T.Unbox t (rep e)
    go (T.Cast t e)             = T.Cast t (rep e)
    go e = e

preCond :: Env -> TExpr -> [Clause TExpr]
preCond env e =
  let name = case texprTyp (contents e) of
        _ -> ""
      _n =  Map.lookup name env
  in []

stmt' :: Env -> [Clause TExpr] -> UnPosTStmt -> ([Clause TExpr], UnPosTStmt)
stmt' env ens = go
  where 
    go (Block ss) = 
      let (cs, s) = mapAccumL (stmt env) ens ss
      in (cs, Block s)
    go (Assign trg src) =
      let newEns = replaceClause ens trg src
      in (newEns, (Assign trg src))
    go (CallStmt e) =
      let pre = preCond env e
          ens' = pre ++ ens 
      in (ens' , CallStmt e)
    go e = error (show e)