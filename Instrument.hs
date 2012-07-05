module Instrument (instrument) where

import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans

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
      let Call trg _ _ _ = contents e
      pre <- lift (liftToEnv $ preCond e)
      posts <- lift (liftToEnv $ texprAssert' featurePost e) -- ignores call chain
      newPre <- weakestPreCall (dConj $ map (teToD (teToDCurr trg)) posts) 
      put (pre ++ [newPre]) -- TODO: perform weakest precondition calculation
      meldCall (CallStmt e)
        
    -- TODO: Deal with until, invariant, and variant as well
    go (Loop from untl inv body var) = do 
        body' <- stmtM body
        from' <- stmtM from
        meldCall (Loop from' untl inv body' var)
    go e = error ("stmt'go: " ++ show e)
  in go

-- | Create weakest precondition expression from a function's postcondition.
-- The input postcondition should be preconverted to the DemonL expression
-- type, including using the correct 'Current' type, probably taken from
-- the originating target of the postcondition's call.
weakestPreCall :: D.Expr -> EnvM D.Expr
weakestPreCall post = do
  qs <- get
  let 
    nonOlds :: [D.Expr]
    nonOlds = nonOldExprs post
      
    existName :: Integer -> String
    existName i = "ex____" ++ show i
    
    replaceUpdated :: D.Expr -> Integer -> D.Expr -> (Integer, D.Expr)
    replaceUpdated nonOldPart i inExpr = 
      let newExpr = replaceExprNoOld (D.Var $ existName i) nonOldPart inExpr
      in (i + 1, newExpr) 
    
    useQuantVar i exprs nonOldPart = mapAccumL (replaceUpdated nonOldPart) i exprs
    
    (post': qs') = snd $ foldl (uncurry useQuantVar) (0, post:qs) nonOlds
  return (D.BinOpExpr D.Implies post' (dConj qs'))

-- | Prefix a statement with a call to demonL with the weakest precondition.
stmtM :: TStmt -> EnvM TStmt
stmtM s = do
  s' <- stmt' (contents s)
  return (attachEmptyPos s')

-- | Gather the subexpressions of a given expression that are non-old.
-- 
-- This may be used to approximate the things that may have changed
-- as specificed by a postcondition.
nonOldExprs :: D.Expr -> [D.Expr]
nonOldExprs = nub . go
  where
    go e@(D.Call _name args) = e : concatMap go args
    go e@(D.Var _) = [e]
    go _ = []

-- | DemonL expression asserting that the given expression isn't null.
dNeqNull :: Pos UnPosTExpr -> D.Expr
dNeqNull e = D.BinOpExpr (D.RelOp D.Neq) (teToDCurr e) D.LitNull

-- | Conjunction of a list of DemonL assertions.
dConj :: [D.Expr] -> D.Expr
dConj [] = D.LitBool True
dConj es = foldr1 (D.BinOpExpr D.And) es

-- | Take an expression and accumulate all preconditions
-- and return them as DemonL expressions.
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

-- | Take a statement and make a new block with the accumulated
-- precondition (stored int the EnvM state) as a rely-call
-- first, then the argument statement.
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

-- | Replace one expression with another in a list of DemonL
-- expressions.
replaceClause :: [D.Expr] -> TExpr -> TExpr -> [D.Expr]
replaceClause clauses old new = 
  map (replaceExpr (teToDCurr old) (teToDCurr new)) clauses  

-- | Instrument a particular statement.
stmt :: Typ -> TInterEnv -> [Decl] -> [D.Expr] -> TStmt -> (TStmt, [D.Expr])
stmt currType env decls ens s = 
  runEnvReader (runStateT (stmtM s) ens) (Env env currType decls)

-- | Instrument a routine body.
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

-- | Instrument a routine.
instrumentRoutine :: TInterEnv
                     -> Typ
                     -> AbsRoutine (RoutineBody TExpr) TExpr 
                     -> AbsRoutine (RoutineBody TExpr) TExpr
instrumentRoutine env typ r = 
  let decls = routineDecls r
  in r {routineImpl = instrumentBody typ env (routineEns r) decls (routineImpl r)}


-- | Instrument a class, but only the given routine name.
instrument :: TInterEnv 
              -> String 
              -> AbsClas (RoutineBody TExpr) TExpr 
              -> AbsClas (RoutineBody TExpr) TExpr
instrument env routName clas = 
  classMapRoutines (\r -> if featureName r == routName
                          then instrumentRoutine env (classToType clas) r
                          else r) clas

