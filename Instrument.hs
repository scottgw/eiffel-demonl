module Instrument (instrument) where

import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans
import Control.Monad.Identity

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

-- | The state monad built on the reader, with the list of assertions
-- for the weakest precondition.
type EnvM = StateT [D.Expr] EnvReaderM

-- | The heart of the instrumentation of statements.
-- Given a statement, a new statement and a list of assertions
-- are returned.
-- The assertions are the weakest precondition calculations,
-- and the new statement has a call inserted before it that
-- goes to the demonic interference tool.
stmt' :: UnPosTStmt -> EnvM UnPosTStmt
stmt' = 
  let
    go :: UnPosTStmt -> EnvM UnPosTStmt
    go (Block blkBody) = do
        blkBody' <- mapM stmtM (reverse blkBody)
        meldCall (Block $ reverse blkBody')
    
    go (Assign trg src) = do
      modify (\ ens -> replaceClause ens trg src)
      meldCall (Assign trg src)
    
    go (CallStmt e) = do
      pre <- lift (liftToEnv $ preCond e)
      posts <- lift (liftToEnv $ texprAssert' featurePost e) -- ignores call chain
      let nonOlds = concatMap nonOldExprs posts
      modify (pre ++) -- TODO: perform weakest precondition calculation
      meldCall (CallStmt e)
        
    -- TODO: Deal with until, invariant, and variant as well
    go (Loop from untl inv body var) = do 
        body' <- stmtM body
        from' <- stmtM from
        meldCall (Loop from' untl inv body' var)
    go e = error ("stmt'go: " ++ show e)
  in go


-- | Prefix a statement with a call to demonL with the weakest precondition.
stmtM :: TStmt -> EnvM TStmt
stmtM s = do
  s' <- stmt' (contents s)
  return (attachEmptyPos s')

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


preCond :: TExpr -> InterfaceReaderM [D.Expr]
preCond = go . contents
  where
    go' = go . contents
    go (T.Call trg name args _) = do
      callPreTExpr <- texprAssert featurePre trg name
      let callPres = map (teToD (teToDCurr trg)) callPreTExpr
      rest <- concatMapM go' (trg : args)
      return (dNeqNull trg : rest ++ callPres)
    go (T.Access trg _ _) = (dNeqNull trg :) `fmap` go' trg
    go (T.Old e) = go' e
    go (T.CurrentVar _)      = return []
    go (T.Attached _ e _)    = go' e
    go (T.Box _ e)     = go' e
    go (T.Unbox _ e)   = go' e
    go (T.Cast _ e)    = go' e
    go (T.Var _ _)     = return []
    go (T.ResultVar _) = return []
    go (T.LitInt _)    = return []
    go (T.LitBool _)   = return []
    go (T.LitVoid _)   = return []
    go (T.LitChar _)   = error "preCond: unimplemented LitChar"
    go (T.LitString _) = error "preCond: unimplemented LitString"
    go (T.LitDouble _) = error "preCond: unimplemented LitDouble"
    go (T.LitArray _)  = error "preCond: unimplemented LitArray"
    go (T.Tuple _)     = error "preCond: unimplemented Tuple"
    go (T.Agent {}) = error "preCond: unimplemented Agent"

meldCall :: UnPosTStmt -> EnvM UnPosTStmt
meldCall s = do
  pre <- get
  Env _ currType decls <- lift $ ask
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
  return (Block [relyCall, p0 s])


p0 :: a -> Pos a
p0 = attachEmptyPos


replaceClause :: [D.Expr] -> TExpr -> TExpr -> [D.Expr]
replaceClause clauses old new = 
  map (replaceExpr (teToDCurr old) (teToDCurr new)) clauses  

-- Top level functions
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
    body' = fst $ stmt currType env decls ensD  body
  in RoutineBody locals localProc body'
instrumentBody _ _ _ _ r = r

stmt :: Typ -> TInterEnv -> [Decl] -> [D.Expr] -> TStmt -> (TStmt, [D.Expr])
stmt currType env decls ens s = 
  runEnvReader (runStateT (stmtM s) ens) (Env env currType decls)



