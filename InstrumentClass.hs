module InstrumentClass where

import Control.Monad.Trans.State

import Data.List (partition)

import qualified Language.DemonL.AST as D
import Language.Eiffel.Syntax as E hiding (select)
import Language.Eiffel.Util
import Language.Eiffel.TypeCheck.TypedExpr as T

import ClassEnv
import Domain
import Util
import Instrument

-- | Instrument a particular statement.
stmt :: Typ -> TInterEnv -> D.Expr -> [Decl] 
        -> [D.Expr] -> TStmt -> (TStmt, [D.Expr])
stmt currType env rely decls ens s = 
  runEnvReader (runStateT (stmtM s) ens) (Env env rely currType decls)

-- | Instrument a routine body.
instrumentBody :: Typ
                  -> TInterEnv 
                  -> Contract TExpr
                  -> [Decl]
                  -> RoutineBody TExpr 
                  -> RoutineBody TExpr
instrumentBody currType env ens decls (RoutineBody locals localProc body) =
  let
    (relies, other) = partition 
                      ((== Just "rely") . clauseName) 
                      (contractClauses ens)
    rely = case relies of
      []  -> D.LitBool True
      r:_ -> teToDCurr (clauseExpr r)
    ensD = map (teToDCurr . clauseExpr) other
    body' = fst $ stmt currType env rely decls ensD  body
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
  withInherit (classMapRoutines updateFeature clas)

  where
    simpleInherit n  = InheritClause (ClassType n []) [] [] [] [] []
    
    addInherit :: [String] -> Inheritance
    addInherit cs = Inheritance False (map simpleInherit cs)

    withInherit clas =
      clas { inherit = 
                addInherit ["PLAN_UTILITIES", "EXTRA_INSTR"] : inherit clas
           }
    
    updateFeature r 
      | featureName r == routName = instrumentRoutine env (classToType clas) r
      | otherwise = r