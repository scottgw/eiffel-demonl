module Main where

import Data.List
import qualified Data.Map as Map
import Data.Map (Map)

import Language.Eiffel.Parser.Parser
import Language.Eiffel.Eiffel as E
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
    go (T.CurrentVar _)         = D.Var "this"
    go (T.Attached _ e _)       =
      let ClassType cn _ = texprTyp (contents e)
          structType = D.StructType cn []
      in D.BinOpExpr (D.RelOp D.Neq structType) (teToD e) D.LitNull
    go (T.Box _ e)     = teToD e
    go (T.Unbox _ e)   = teToD e
    go (T.Cast _ e)    = teToD e
    go (T.Var n _)     = D.Var n
    go (T.ResultVar _) = D.ResultVar
    go (T.LitInt i)    = D.LitInt i
    go (T.LitBool b)   = D.LitBool b
    go (T.LitVoid _)   = D.LitNull
    go (T.LitChar _)   = error "teToD: unimplemented LitChar"
    go (T.LitString _) = error "teToD: unimplemented LitString"
    go (T.LitDouble _) = error "teToD: unimplemented LitDouble"
    
dNeqNull e =       
  let ClassType cn _ = texprTyp (contents e)
      structType = D.StructType cn []
  in D.BinOpExpr (D.RelOp D.Neq structType) (teToD e) D.LitNull

dConj :: [D.Expr] -> D.Expr
dConj = foldr1 (D.BinOpExpr D.And)

texprClassName :: TExpr -> String
texprClassName e = 
  let ClassType cn _ = texprTyp (contents e)
  in cn

texprInterface :: Env -> TExpr -> ClasInterface
texprInterface env e = 
  case Map.lookup (texprClassName e) env of
    Just ci -> ci
    Nothing -> error $ "texprInterface: " ++ show e

texprPre :: Env -> TExpr -> String -> [T.TExpr]
texprPre env targ name = 
  let iface = texprInterface env targ
  in case typedPre (Map.elems env) iface name of
    Right contract -> map (clauseExpr) (contractClauses contract)
    Left e -> error $ "texprPre: " ++ e

preCond :: Env -> TExpr -> [D.Expr]
preCond env e = go (contents e)
  where
    go (T.Call trg name args _) = 
      let callPreTExpr = texprPre env trg name
          callPres = map teToD callPreTExpr
      in dNeqNull trg : (concatMap (preCond env) (trg : args)) ++ callPres
    go (T.Access trg name _)    = dNeqNull trg : preCond env trg
    go (T.BinOpExpr op e1 e2 _) = [] -- TODO: at least handle division by 0
    go (T.UnOpExpr op e _)      = [] -- TODO: lookup the operator
    go (T.CurrentVar _)         = []
    go (T.Attached _ e _)       = preCond env e
    go (T.Box _ e)     = preCond env e
    go (T.Unbox _ e)   = preCond env e
    go (T.Cast _ e)    = preCond env e
    go (T.Var n _)     = []
    go (T.ResultVar _) = []
    go (T.LitInt i)    = []
    go (T.LitBool b)   = []
    go (T.LitVoid _)   = []
    go (T.LitChar _)   = error "teToD: unimplemented LitChar"
    go (T.LitString _) = error "teToD: unimplemented LitString"
    go (T.LitDouble _) = error "teToD: unimplemented LitDouble"

meldCall :: [D.Expr] -> UnPosTStmt -> ([D.Expr], UnPosTStmt)
meldCall pre s = 
  let 
    chk :: TStmt
    chk = p0 $ Check 
          [Clause Nothing 
             (p0 $ T.LitString $ "condition: " ++ show (dConj $ nub $ pre))]
  in (pre, Block [chk, p0 s])

stmt' :: Env -> [D.Expr] -> UnPosTStmt -> ([D.Expr], UnPosTStmt)
stmt' env ens = go
  where 
    go (Block blkBody) = 
      let (cs, blkBody') = wpList ens blkBody -- mapAccumR (stmt env) ens ss
          wpList p [] = (p, [])
          wpList p (s:ss) = 
            let (p', ss') = wpList p ss
                (p'', s') = stmt env p' s
            in (p'', s':ss')
      in meldCall cs (Block blkBody')
    go (Assign trg src) =
      let newEns = replaceClause ens trg src
      in meldCall newEns (Assign trg src)
    go (CallStmt e) =
      let pre = preCond env e
          ens' = pre ++ ens -- TODO: perform weakest precondition calculation
      in meldCall ens' (CallStmt e)
         
    -- TODO: Deal with until, invariant, and variant as well
    go (Loop from untl inv body var) =
      let 
        (bodyCls, body') = stmt env ens body
        (fromCls, from') = stmt env bodyCls from
      in meldCall fromCls (Loop from' untl inv body' var)
    go e = error ("stmt'go: " ++ show e)
