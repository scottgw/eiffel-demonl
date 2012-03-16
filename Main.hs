module Main where

import Data.Either
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe

import Language.Eiffel.Parser.Parser
import Language.Eiffel.Syntax as E
import Language.Eiffel.Util
import Language.Eiffel.Position
import qualified Language.Eiffel.PrettyPrint as PP

import Language.Eiffel.TypeCheck.Class
import Language.Eiffel.TypeCheck.TypedExpr as T

import qualified Language.DemonL.AST as D
import qualified Language.DemonL.Types as D

import System.Directory
import System.FilePath

import ClassEnv
import DepGen
import Domain
import GenerateSummaries

main :: IO ()
main = do
  currDir <- getCurrentDirectory
  let testDir = currDir </> "test"
  --  print searchDirectories
  -- files <- collectFileMap (testDir : searchDirectories)
  -- print files
  classEi <- parseClassFile (testDir </> "work_queue.e")
  case classEi of
    Left e -> print e
    Right cls -> do
      classInts <- Map.elems `fmap` readAllSummaries -- depGenInt files (className cls)
      putStrLn "Generated dependencies"
      let unliked = rights (map (unlikeInterfaceM classInts) classInts)
      let domainInts = either (error . show) id $ depGen (makeEnv unliked) "work_queue"
      print (map className domainInts)
      case clasM classInts cls of
        Left e -> print e
        Right typedClass ->
          case typeInterfaces domainInts of
            Left err -> print err
            Right typedInts ->
              print (PP.toDoc $ untype $ 
                     instrument (makeEnv typedInts) "dequeue" typedClass)


instrument :: TInterEnv -> String -> AbsClas (RoutineBody TExpr) TExpr 
              -> AbsClas (RoutineBody TExpr) TExpr
instrument env routName = 
  classMapRoutines (\r -> if featureName r == routName
                          then instrumentRoutine env r
                          else r)

instrumentRoutine :: TInterEnv -> AbsRoutine (RoutineBody TExpr) TExpr 
                     -> AbsRoutine (RoutineBody TExpr) TExpr
instrumentRoutine env r = 
  r {routineImpl = instrumentBody env (routineEns r) (routineImpl r)}

instrumentBody :: TInterEnv -> Contract TExpr 
                  -> RoutineBody TExpr -> RoutineBody TExpr
instrumentBody env ens (RoutineBody locals localProc body) =
  let 
    ensD = map (teToD . clauseExpr) (contractClauses ens)
    body' = snd $ stmt env [] ensD  body
  in RoutineBody locals localProc body'
instrumentBody _ _ r = r

stmt :: TInterEnv -> [Decl] -> [D.Expr] -> TStmt -> ([D.Expr], TStmt)
stmt env decls ens s = 
  let (cs, s') = stmt' env decls ens (contents s)
  in (cs, attachEmptyPos s')


p0 :: a -> Pos a
p0 = attachEmptyPos

dummyExpr :: Pos (AbsStmt (Pos UnPosTExpr))
dummyExpr =
  let trg = p0 $ Var "mutex" (ClassType "MUTEX" []) 
      call = p0 $ Call trg "lock" [] NoType
      s = p0 $ CallStmt call
  in s

block :: (t, [PosAbsStmt a]) -> (t, AbsStmt a)
block (cs, s) = (cs, Block s)

replaceClause :: [D.Expr] -> TExpr -> TExpr -> [D.Expr]
replaceClause clauses old new = 
  map (replaceExpr (teToD old) (teToD new)) clauses
  
replaceExpr :: D.Expr -> D.Expr -> D.Expr -> D.Expr
replaceExpr new old = go
  where 
    rep = replaceExpr new old
    go e | e == old           = new
    go (D.Call name args)     = D.Call name (map rep args)
    go (D.Access trg name)    = D.Access (rep trg) name
    go (D.BinOpExpr op e1 e2) = D.BinOpExpr op (rep e1) (rep e2)
    go (D.UnOpExpr op e)      = D.UnOpExpr op (rep e)
    go e = e

dNeqNull :: Pos UnPosTExpr -> D.Expr
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

texprInterface :: TInterEnv -> TExpr -> AbsClas EmptyBody T.TExpr
texprInterface env e = 
  fromMaybe (error $ "texprInterface: " ++ show e) 
            (envLookup (texprClassName e) env)

texprPre :: TInterEnv -> TExpr -> String -> [T.TExpr]
texprPre env targ name = 
  let iface = texprInterface env targ
  in case findFeature iface name of
    Just rout -> map clauseExpr (contractClauses (routineReq rout))
    Nothing -> error $ "texprPre: can't find routine"

preCond :: TInterEnv -> TExpr -> [D.Expr]
preCond env ex = go (contents ex)
  where
    go' = go . contents
    go (T.Call trg name args _) = 
      let callPreTExpr = texprPre env trg name
          callPres = map teToD callPreTExpr
      in dNeqNull trg : concatMap go' (trg : args) ++ callPres
    go (T.Access trg _ _) = dNeqNull trg : go' trg
    go (T.Old e) = go' e
    go (T.CurrentVar _)      = []
    go (T.Attached _ e _)    = go' e
    go (T.Box _ e)     = go' e
    go (T.Unbox _ e)   = go' e
    go (T.Cast _ e)    = go' e
    go (T.Var _ _)     = []
    go (T.ResultVar _) = []
    go (T.LitInt _)    = []
    go (T.LitBool _)   = []
    go (T.LitVoid _)   = []
    go (T.LitChar _)   = error "preCond: unimplemented LitChar"
    go (T.LitString _) = error "preCond: unimplemented LitString"
    go (T.LitDouble _) = error "preCond: unimplemented LitDouble"
    go (T.LitArray _)  = error "preCond: unimplemented LitArray"
    go (T.Tuple _)     = error "preCond: unimplemented Tuple"
    go (T.Agent _)     = error "preCond: unimplemented Agent"

meldCall :: [Decl] -> [D.Expr] -> UnPosTStmt -> ([D.Expr], UnPosTStmt)
meldCall decls pre s = 
  let 
    tuple x y = p0 $ T.Tuple [x, y]
    curr = p0 $ T.CurrentVar NoType

    string :: String -> T.TExpr
    string name = p0 $ T.LitString name

    var name = p0 $ T.Var name NoType

    varTuple :: String -> T.TExpr
    varTuple name = tuple (string name) (var name)

    array :: [T.TExpr] -> T.TExpr
    array = p0 . T.LitArray

    rely :: [T.TExpr] -> T.TExpr
    rely es = p0 $ T.Call curr "rely_call" es NoType

    precondStr = show $ dConj $ nub pre

    agent = p0 . T.Agent

    declTup (Decl n _) = varTuple n

    declArray :: T.TExpr
    declArray = array (map declTup decls)

    args :: [T.TExpr]
    args = [declArray, string precondStr]

    relyCall :: TStmt
    relyCall = p0 $ E.CallStmt $ rely args
  in (pre, Block [relyCall, p0 s])

stmt' :: TInterEnv -> [Decl] -> [D.Expr] -> UnPosTStmt -> ([D.Expr], UnPosTStmt)
stmt' env decls ens = go
  where 
    go :: UnPosTStmt -> ([D.Expr], UnPosTStmt)
    go (Block blkBody) = 
      let (cs, blkBody') = wpList ens blkBody -- mapAccumR (stmt env) ens ss
          wpList p [] = (p, [])
          wpList p (s:ss) = 
            let (p', ss') = wpList p ss
                (p'', s') = stmt env decls p' s
            in (p'', s':ss')
      in meldCall decls cs (Block blkBody')
    
    go (Assign trg src) =
      let newEns = replaceClause ens trg src
      in meldCall decls newEns (Assign trg src)
    
    go (CallStmt e) =
      let pre = preCond env e
          ens' = pre ++ ens -- TODO: perform weakest precondition calculation
      in meldCall decls ens' (CallStmt e)
         
    -- TODO: Deal with until, invariant, and variant as well
    go (Loop from untl inv body var) =
      let 
        (bodyCls, body') = stmt env decls ens body
        (fromCls, from') = stmt env decls bodyCls from
      in meldCall decls fromCls (Loop from' untl inv body' var)
    go e = error ("stmt'go: " ++ show e)
