module Instrument (instrument) where

import Data.List

import Language.Eiffel.Syntax as E hiding (select)
import Language.Eiffel.Util
import Language.Eiffel.Position

import Language.Eiffel.TypeCheck.TypedExpr as T

import qualified Language.DemonL.AST as D
import Language.DemonL.PrettyPrint

import ClassEnv
import Domain
import Util

stmt' :: Typ -> TInterEnv 
         -> [Decl] -> [D.Expr] 
         -> UnPosTStmt -> ([D.Expr], UnPosTStmt)
stmt' curr env decls ens = go
  where 
    meld = meldCall curr decls
    
    go' = stmt curr env decls
    
    go :: UnPosTStmt -> ([D.Expr], UnPosTStmt)
    go (Block blkBody) = 
      let (cs, blkBody') = wpList ens blkBody -- mapAccumR (stmt env) ens ss
          wpList p [] = (p, [])
          wpList p (s:ss) = 
            let (p', ss') = wpList p ss
                (p'', s') = go' p' s
            in (p'', s':ss')
      in meld cs (Block blkBody')
    
    go (Assign trg src) =
      let newEns = replaceClause ens trg src
      in meld newEns (Assign trg src)
    
    go (CallStmt e) =
      let pre = preCond env e
          posts :: [T.TExpr]
          posts = texprAssert' featurePost env e -- ignores call chain
          nonOlds = concatMap nonOldExprs posts
          ens' = pre ++ ens -- TODO: perform weakest precondition calculation
      in meld ens' (CallStmt e)
         
    -- TODO: Deal with until, invariant, and variant as well
    go (Loop from untl inv body var) =
      let 
        (bodyCls, body') = go' ens body
        (fromCls, from') = go' bodyCls from
      in meld fromCls (Loop from' untl inv body' var)
    go e = error ("stmt'go: " ++ show e)

instrument :: TInterEnv 
              -> String 
              -> AbsClas (RoutineBody TExpr) TExpr 
              -> AbsClas (RoutineBody TExpr) TExpr
instrument env routName clas = 
  classMapRoutines (\r -> if featureName r == routName
                          then instrumentRoutine env (classToType clas) r
                          else r) clas

instrumentRoutine :: TInterEnv
                     -> Typ
                     -> AbsRoutine (RoutineBody TExpr) TExpr 
                     -> AbsRoutine (RoutineBody TExpr) TExpr
instrumentRoutine env typ r = 
  let decls = routineDecls r
  in r {routineImpl = instrumentBody typ env (routineEns r) decls (routineImpl r)}

instrumentBody :: Typ
                  -> TInterEnv 
                  -> Contract TExpr
                  -> [Decl]
                  -> RoutineBody TExpr 
                  -> RoutineBody TExpr
instrumentBody currType env ens decls (RoutineBody locals localProc body) =
  let 
    ensD = map (teToDCurr . clauseExpr) (contractClauses ens)
    body' = snd $ stmt currType env decls ensD  body
  in RoutineBody locals localProc body'
instrumentBody _ _ _ _ r = r

stmt :: Typ -> TInterEnv -> [Decl] -> [D.Expr] -> TStmt -> ([D.Expr], TStmt)
stmt currType env decls ens s = 
  let (cs, s') = stmt' currType env decls ens (contents s)
  in (cs, attachEmptyPos s')

nonOldExprs :: T.TExpr -> [T.UnPosTExpr]
nonOldExprs = nub . go'
  where
    go' :: T.TExpr -> [T.UnPosTExpr]
    go' = go . contents
    
    go e@(T.Call _trg _name args _) = e : concatMap go' args
    go e@(Var _ _) = [e]
    go _ = []


dNeqNull :: Pos UnPosTExpr -> D.Expr
dNeqNull e = D.BinOpExpr (D.RelOp D.Neq) (teToDCurr e) D.LitNull

dConj :: [D.Expr] -> D.Expr
dConj = foldr1 (D.BinOpExpr D.And)


preCond :: TInterEnv -> TExpr -> [D.Expr]
preCond env = go . contents
  where
    go' = go . contents
    go (T.Call trg name args _) = 
      let callPreTExpr = texprAssert featurePre env trg name
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

meldCall :: Typ -> [Decl] -> [D.Expr] -> UnPosTStmt -> ([D.Expr], UnPosTStmt)
meldCall currType decls pre s = 
  let 
    tuple x y = p0 $ T.Tuple [x, y]
    curr = p0 $ T.CurrentVar currType

    string :: String -> T.TExpr
    string name = p0 $ T.LitString name

    var name t = p0 $ T.Var name t

    array :: [T.TExpr] -> T.TExpr
    array = p0 . T.LitArray

    rely :: [T.TExpr] -> T.TExpr
    rely es = p0 $ T.Call curr "rely_call" es NoType

    precondStr = show $ untypeExprDoc $ dConj $ nub pre

    _agent = p0 . T.Agent

    declTup (Decl n t) = tuple (string n) (var n t)

    declArray :: T.TExpr
    declArray = 
      array (tuple (string "this") curr : map declTup decls)

    args :: [T.TExpr]
    args = [declArray, string precondStr]

    relyCall :: TStmt
    relyCall = p0 $ E.CallStmt $ rely args
  in (pre, Block [relyCall, p0 s])


p0 :: a -> Pos a
p0 = attachEmptyPos


replaceClause :: [D.Expr] -> TExpr -> TExpr -> [D.Expr]
replaceClause clauses old new = 
  map (replaceExpr (teToDCurr old) (teToDCurr new)) clauses  
