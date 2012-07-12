module InstrumentClass where

import Control.Monad.Trans.State

import qualified Language.DemonL.AST as D
import Language.Eiffel.Syntax as E hiding (select)
import Language.Eiffel.Util
import Language.Eiffel.TypeCheck.TypedExpr as T

import ClassEnv
import Domain
import Util
import Instrument

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

