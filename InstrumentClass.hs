{-# LANGUAGE OverloadedStrings #-}
module InstrumentClass where

import Control.Monad.Trans.State

import           Data.List (partition)
import qualified Data.Text as Text
import           Data.Text (Text)

import qualified Language.DemonL.AST as D
import qualified Language.DemonL.TypeCheck as DT
import           Language.Eiffel.Syntax as E hiding (select)
import qualified Language.Eiffel.Util as E
import           Language.Eiffel.TypeCheck.TypedExpr as T

import           ClassEnv
import           Domain
import           Util
import           Instrument

-- | Instrument a particular statement.
stmt :: Typ -> Typ -> TInterEnv -> DT.TExpr -> [Decl] 
        -> [DT.TExpr] -> TStmt -> (TStmt, [DT.TExpr])
stmt currType resType env rely decls ens s = 
  runEnvReader (runStateT (stmtM s) ens) (Env env rely currType resType decls)

-- | Instrument a routine body.
instrumentBody :: Typ
                  -> Typ
                  -> TInterEnv 
                  -> Contract TExpr
                  -> [Decl]
                  -> RoutineBody TExpr 
                  -> RoutineBody TExpr
instrumentBody currType resType env ens decls (RoutineBody locals localProc body) =
  let
    (relies, other) = partition 
                      ((== Just "rely") . clauseName) 
                      (contractClauses ens)
    rely = case relies of
      []  -> DT.LitBool True
      r:_ -> teToDCurr (fromType currType) (clauseExpr r)
    ensD = map (teToDCurr (fromType currType) . clauseExpr) other
    body' = fst $ stmt currType resType env rely decls ensD  body
  in RoutineBody locals localProc body'
instrumentBody _ _ _ _ _ r = r

-- | Instrument a routine.
instrumentRoutine :: TInterEnv
                     -> Typ
                     -> AbsRoutine (RoutineBody TExpr) TExpr 
                     -> AbsRoutine (RoutineBody TExpr) TExpr
instrumentRoutine env typ r = 
  let decls = E.routineDecls r
      resType = E.featureResult r
  in r {routineImpl = instrumentBody typ resType env (routineEns r) decls (routineImpl r)}


-- | Instrument a class, but only the given routine name.
instrument :: TInterEnv 
              -> Text
              -> AbsClas (RoutineBody TExpr) TExpr 
              -> AbsClas (RoutineBody TExpr) TExpr
instrument env routName class_ = 
  withInherit (E.classMapRoutines updateFeature class_)

  where
    simpleInherit n  = InheritClause (ClassType n []) [] [] [] [] []
    
    addInherit :: [Text] -> Inheritance
    addInherit cs = Inheritance False (map simpleInherit cs)

    withInherit c =
      c { inherit = 
             addInherit ["PLAN_UTILITIES"] : inherit c
        }
    
    updateFeature r 
      | E.featureName r == routName = 
        instrumentRoutine env (E.classToType class_) r
      | otherwise = r