module EiffelBuilder where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Language.Eiffel.Syntax
import Language.Eiffel.Position
import Language.Eiffel.Util

import qualified Language.Eiffel.TypeCheck.TypedExpr as T

-- Syntax building functions
p0 = attachEmptyPos

-- Statements
do_ = block
block = p0 . Block
callStmt trg str args = callS (call trg str args)
callS = p0 . CallStmt
if_ c then_ elseIfs elseMb = p0 $ If c then_ elseIfs elseMb
ifs ((cond, stmt):cs) = if_ cond stmt (map (uncurry ElseIfPart) cs) Nothing
elseIf c then_ = p0 $ ElseIfPart c then_
str .= e = p0 $ Assign str e

infix 2 .=


-- untyped expressions
sType name = ClassType name []
current = p0 CurrentVar
var = p0 . VarOrCall
call trg str args = p0 (QualCall trg str args)
trg .@ str = call trg str
callTrg .< args = callTrg args

e1 .+ e2 = p0 (BinOpExpr Add e1 e2)
eStr = p0 . LitString
attached tMb e strMb = p0 (Attached tMb e strMb)


-- typed expressions
tupleT= p0 . T.Tuple
currVarT= p0 . T.CurrentVar

arrayT :: [T.TExpr] -> T.TExpr
arrayT = p0 . T.LitArray
        

stringT :: String -> T.TExpr
stringT = p0 . T.LitString

varT name t = p0 $ T.Var name t

-- modification functions

addFeatureToClause feat = FeatureClause [] [feat] [] []

addFeature cls feat = 
  cls { featureClauses = addFeatureToClause feat : featureClauses cls }

-- addFeature cls feat = 
--   cls { featureMap = Map.insert (featureName feat) 
--                                 (ExportedFeature Set.empty (SomeRoutine feat)) 
--                                 (featureMap cls)
--       }

-- empty classes and routines to fill
emptyClass name =
  AbsClas
      { frozenClass   = False
      , expandedClass = False
      , deferredClass = False
      , classNote     = []
      , className     = name
      , currProc      = Dot
      , procGeneric   = []
      , procExpr      = []
      , generics      = []
      , obsoleteClass = False
      , inherit       = []
      , creates       = []
      , converts      = []
      , featureClauses = []
      , invnts        = []
      }

emptyRoutine name =
  AbsRoutine
    { routineFroz     = False
    , routineName     = name
    , routineAlias    = Nothing
    , routineArgs     = []
    , routineResult   = NoType
    , routineAssigner = Nothing
    , routineNote     = []
    , routineProcs    = []
    , routineReq      = (Contract False [])
    , routineReqLk    = []
    , routineImpl     = ()
    , routineEns      = (Contract False [])
    , routineEnsLk    = []
    , routineRescue   = Nothing
    }

emptyFeatureClause f = 
  FeatureClause
    { exportNames = []
    , routines    = [f]
    , attributes  = []
    , constants   = []
                   }
