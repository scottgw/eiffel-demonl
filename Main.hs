module Main where

import Data.List
import qualified Data.Map as Map
import Data.Map (Map)

import Language.Eiffel.Parser.Parser
import Language.Eiffel.Eiffel
import qualified Language.Eiffel.PrettyPrint as PP
import Language.Eiffel.TypeCheck.Class
import Language.Eiffel.TypeCheck.TypedExpr as T

import qualified Language.DemonL.AST as D
import qualified Language.DemonL.Types as D

import System.Directory
import System.FilePath

import DepGen

srcPath = ["/","home","scott","src"]
localPath = ["/","home","scott","local"]
libraryPath = localPath ++ ["Eiffel70","library"]

searchDirectories = 
  map joinPath 
    [ srcPath ++ ["eiffelbase2","trunk"]
    , libraryPath ++ ["base","elks"]
    , libraryPath ++ ["thread","classic"]
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




instrument env routName = 
  classMapRoutines (\r -> if featureName r == routName
                          then instrumentRoutine env r
                          else r)

instrumentRoutine :: Env -> AbsRoutine RoutineBody TExpr 
                     -> AbsRoutine RoutineBody TExpr
instrumentRoutine env r = 
  r {routineImpl = instrumentBody env (routineEns r) (routineImpl r)}

instrumentBody :: Env -> Contract TExpr 
                  -> RoutineBody TExpr -> RoutineBody TExpr
instrumentBody env ens (RoutineBody locals localProc body) =
  let 
    ensD = map (teToD . clauseExpr) (contractClauses ens)
    body' = snd $ stmt env ensD  body
  in RoutineBody locals localProc body'
instrumentBody _ _ r = r

stmt :: Env -> [D.Expr] -> TStmt -> ([D.Expr], TStmt)
stmt env ens s = 
  let (cs, s') = stmt' env ens (contents s)
  in (cs, attachEmptyPos s')

p0 = attachEmptyPos

dummyExpr =
  let trg = p0 $ Var "mutex" (ClassType "MUTEX" []) 
      call = p0 $ Call trg "lock" [] NoType
      s = p0 $ CallStmt call
  in s
     
type Env = Map String ClasInterface

block (cs, s) = (cs, Block s)

replaceClause :: [D.Expr] -> TExpr -> TExpr -> [D.Expr]
replaceClause clauses old new = 
  map (replaceExpr (teToD old) (teToD new)) clauses
  
  
replaceExpr :: D.Expr -> D.Expr -> D.Expr -> D.Expr
replaceExpr new old = go
  where 
    rep = replaceExpr new old
    go (D.Call name args)     = D.Call name (map rep args)
    go (D.Access trg name)    = D.Access (rep trg) name
    go (D.BinOpExpr op e1 e2) = D.BinOpExpr op (rep e1) (rep e2)
    go (D.UnOpExpr op e)      = D.UnOpExpr op (rep e)
    go e = e


op1 Not = D.Not
op1 Neg = D.Neg
op1 Old = D.Old
op1 Sqrt = error "teToD: unimpleneted Sqrt"
    
op2 Add = D.Add
op2 Sub = D.Sub
op2 Mul = D.Mul
op2 Div = D.Div
op2 Or  = D.Or
op2 And = D.And
op2 OrElse = D.Or
op2 AndThen = D.And
op2 Xor = D.RelOp D.Neq D.BoolType
op2 Implies = D.Implies
op2 (RelOp r _) = D.RelOp (rel r) D.NoType
    
rel Eq = D.Eq
rel Neq = D.Neq
rel Lte = D.Lte
rel Lt = D.Lt
rel Gt = D.Gt
rel Gte = D.Gte
rel TildeEq = D.Eq
rel TildeNeq = D.Neq

teToD :: TExpr -> D.Expr
teToD te = go (contents te)
  where
    go (T.Call trg name args _) = D.Call name (teToD trg : map teToD args)
    go (T.Access trg name _)    = D.Access (teToD trg) name
    go (T.BinOpExpr op e1 e2 _) = D.BinOpExpr (op2 op) (teToD e1) (teToD e2)
    go (T.UnOpExpr op e _)      = D.UnOpExpr (op1 op) (teToD e)
    go (T.Attached _ e _)       =
      let ClassType cn _ = texprTyp (contents e)
          structType = D.StructType cn []
      in D.BinOpExpr (D.RelOp D.Neq structType) (teToD e) D.LitNull
    go (T.Box _ e)              = teToD e
    go (T.Unbox _ e)            = teToD e
    go (T.Cast _ e)             = teToD e
    go (T.Var n _)     = D.Var n
    go (T.ResultVar _) = D.ResultVar
    go (T.LitInt i)    = D.LitInt i
    go (T.LitBool b)   = D.LitBool b
    go (T.LitVoid _)   = D.LitNull
    go (T.LitChar _)   = error "teToD: unimplemented LitChar"
    go (T.LitString _) = error "teToD: unimplemented LitString"
    go (T.LitDouble _) = error "teToD: unimplemented LitDouble"

-- eToD :: Expr -> D.Expr
-- eToD te = go (contents te)
--   where
--     go (T.Call trg name args _) = D.Call name (eToD trg : map eToD args)
--     go (T.Access trg name _)    = D.Access (eToD trg) name
--     go (T.BinOpExpr op e1 e2 _) = D.BinOpExpr (op2 op) (eToD e1) (eToD e2)
--     go (T.UnOpExpr op e _)      = D.UnOpExpr (op1 op) (eToD e)
--     go (T.Attached _ e _)       =
--       let ClassType cn _ = texprTyp (contents e)
--           structType = D.StructType cn []
--       in D.BinOpExpr (D.RelOp D.Neq structType) (eToD e) D.LitNull
--     go (T.Box _ e)              = eToD e
--     go (T.Unbox _ e)            = eToD e
--     go (T.Cast _ e)             = eToD e
--     go (T.Var n _)     = D.Var n
--     go (T.ResultVar _) = D.ResultVar
--     go (T.LitInt i)    = D.LitInt i
--     go (T.LitBool b)   = D.LitBool b
--     go (T.LitVoid _)   = D.LitNull
--     go (T.LitChar _)   = error "eToD: unimplemented LitChar"
--     go (T.LitString _) = error "eToD: unimplemented LitString"
--     go (T.LitDouble _) = error "eToD: unimplemented LitDouble"


preCond :: Env -> TExpr -> [D.Expr]
preCond env e =
  let name = case texprTyp (contents e) of
        _ -> ""
      _n =  Map.lookup name env
  in []

stmt' :: Env -> [D.Expr] -> UnPosTStmt -> ([D.Expr], UnPosTStmt)
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
--    go e = error (show e)
