module Main where

import Control.Applicative

import Data.Binary
import qualified Data.ByteString.Lazy as BS
import Data.List

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)


import Data.Maybe

import Language.Eiffel.Parser.Parser
import Language.Eiffel.Syntax as E
import Language.Eiffel.Util
import Language.Eiffel.Position
import qualified Language.Eiffel.PrettyPrint as PP

import Language.Eiffel.TypeCheck.Class
import Language.Eiffel.TypeCheck.Expr (flatten)
import Language.Eiffel.TypeCheck.Context
import Language.Eiffel.TypeCheck.TypedExpr as T

import qualified Language.DemonL.AST as D
import qualified Language.DemonL.Types as D

import System.Directory
import System.FilePath

import ClassEnv
import DepGen
import Domain
import GenerateSummaries

getDomain file = do
  classEi <- parseClassFile file
  case classEi of
    Left err -> error $ "getDomain: " ++  show err
    Right cls -> do
      classInts <- Map.elems `fmap` readAllSummaries
      case depGen (makeEnv classInts) "work_queue" of
        Left err -> error $ "getDomain: " ++ show err
        Right domainInts -> 
          case clasM classInts cls of 
            Left err -> error $ "getDomain: " ++  err
            Right tCls -> do
              tis <- typeInterfaces domainInts
              return (tis, tCls)


getDomainFile file = do 
  classEi <- parseClassFile file
  case classEi of
    Left err -> error $ "getDomain: " ++  show err
    Right cls -> do
      classInts <- Map.elems `fmap` readAllSummaries
      domainInts <- readDomain
      case clasM classInts cls of 
        Left err -> error $ "getDomain: " ++  err
        Right tCls -> return (domainInts, tCls)

readDomain :: IO ([AbsClas EmptyBody T.TExpr])
readDomain = decode <$> BS.readFile "typed_domain.tdom"

writeDomain file = do
  (Right tis, _) <- getDomain file
  BS.writeFile "typed_domain.tdom" $ encode tis

main :: IO ()
main = do
  currDir <- getCurrentDirectory
  let testFile = currDir </> "test" </> "work_queue.e"
  (typedDomain, typedClass) <- getDomainFile testFile
  print (PP.toDoc $ untype $ 
         instrument (flattenEnv $ makeEnv typedDomain) "dequeue" typedClass)

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
    ensD = map (teToDCurr . clauseExpr) (contractClauses ens)
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
  map (replaceExpr (teToDCurr old) (teToDCurr new)) clauses
  
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
  in D.BinOpExpr (D.RelOp D.Neq structType) (teToDCurr e) D.LitNull

dConj :: [D.Expr] -> D.Expr
dConj = foldr1 (D.BinOpExpr D.And)

texprClassName :: TExpr -> String
texprClassName e = 
  let ClassType cn _ = texprTyp (contents e)
  in cn

texprInterface :: TInterEnv -> TExpr -> AbsClas EmptyBody T.TExpr
texprInterface env e = 
  fromMaybe (error $ "texprInterface: " ++ show e ++ "," ++ show (envKeys env))
            (envLookup (texprClassName e) env)

texprPre :: TInterEnv -> TExpr -> String -> [T.TExpr]
texprPre env targ name = 
  let 
    ClassType typeName _ = texpr targ
    Just iface = envLookup typeName env
  in case findFeatureEx iface name of
    Just feat -> map clauseExpr (featurePre feat)
    Nothing -> error $ "texprPre: can't find feature: " ++ show targ ++ "." ++ name

preCond :: TInterEnv -> TExpr -> [D.Expr]
preCond env ex = go (contents ex)
  where
    go' = go . contents
    go (T.Call trg name args _) = 
      let callPreTExpr = texprPre env trg name
          callPres = map (teToD (teToDCurr trg)) callPreTExpr
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
    go (T.Agent _ _ _ _) = error "preCond: unimplemented Agent"

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


data Indicator = Indicator Typ String deriving (Eq, Ord)
data Action = Action Typ String deriving (Eq, Ord)


flattenEnv :: TInterEnv -> TInterEnv
flattenEnv env@(ClassEnv m) = 
  ClassEnv (Map.map (flatten' env . classToType) m)
  where
    flatten' :: TInterEnv -> Typ -> AbsClas EmptyBody T.TExpr
    flatten' (ClassEnv e) typ = 
      case idErrorRead (flatten typ) (mkCtx typ (Map.elems e)) of
        Left e -> error $ "flatten': " ++ e
        Right c -> classMapExprs updRoutine id id c
      where
        updRoutine r = r { routineReq = updContract (routineReq r)
                         , routineEns = updContract (routineEns r)
                         }
        updContract = mapContract (\cl -> cl {clauseExpr = go' (clauseExpr cl)})
      
        go' e = attachPos (position e) (go $ contents e)
        go (T.Call trg n args t) = T.Call (go' trg) n (map go' args) t
        go (T.CurrentVar t) = T.CurrentVar typ
  
  
domActions :: TInterEnv -> T.TExpr -> Set Action
domActions env e = 
  let indicators = exprIndicators e
      -- Desired interface:
      domActions' :: Set Indicator -> Set Action
      domActions' = Set.fold (Set.union . go) Set.empty
        where
          go :: Indicator -> Set Action
          go ind@(Indicator typ name) = 
            let Just clas = envLookup (classNameType typ) env
                routines = allRoutines clas
                hasIndicator = Set.member ind .  clausesIndicators . featurePre
                modifyIndicators = filter hasIndicator routines
            in Set.fromList (map (\r -> Action typ (featureName r)) 
                                 modifyIndicators)
  in domActions' indicators

clausesIndicators :: [Clause T.TExpr] -> Set Indicator
clausesIndicators = Set.unions . map (exprIndicators . clauseExpr)

exprIndicators :: T.TExpr -> Set Indicator
exprIndicators = go'
  where go' = go . contents
        go (T.Call trg name args t) = 
          let argPairs = Set.unions (map exprIndicators (trg : args))
          in Set.insert (Indicator (texpr trg) name) argPairs
        go _ = Set.empty