module SpecialSerialization where

import Language.Eiffel.Syntax
import Language.Eiffel.Position

import qualified Data.Set as Set
import Data.Set (Set)

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

addFeatureClause cls f = cls {featureClauses = f : featureClauses cls}



type ExtractFeatures = (Typ, Set String)

extractClass :: [ExtractFeatures] -> Clas
extractClass extrFeatures = addFeatureClause base featClause
  where
    base = emptyClass "EXTRA_INSTR"
    featClause = FeatureClause
                   { exportNames = []
                   , routines    = [extractProcess extrFeatures]
                   , attributes  = []
                   , constants   = []
                   }

extractProcess :: [ExtractFeatures] -> Routine
extractProcess extrFeatures = withArgs
  where
    base     = emptyRoutine "extra_instr"
    withBody = 
      base {routineImpl = 
               RoutineBody
                  { routineLocal      = []
                  , routineLocalProcs = []
                  , routineBody       = block (extractStmts extrFeatures)
                  }
           }
    args     = [ Decl "a_obj" (sType "ANY")
               , Decl "a_name" (sType "STRING")
               , Decl "serizer" (sType "SEXPR_SERIALIZER")
               ]
    withArgs = withBody {routineArgs = args}

extractStmts :: [ExtractFeatures] -> [Stmt]
extractStmts = concatMap go 
  where go (t, funcs) = Set.toList (Set.map (extractStmt t) funcs)

extractStmt :: Typ -> String -> Stmt
extractStmt targ feature = 
  p0 $ If cond then_ [] Nothing
  where
    ClassType typeName gens = targ
    targ' = ClassType typeName (map (const (sType "ANY")) gens)
    cond = p0 $ Attached (Just targ') (var "a_obj") (Just "cast_obj")
    then_ = callStmt (var "serizer")
            -- FIXME: This serialize method should represent the demonL as a
            -- function call, not an attribute.
                     "serialize_attr"
                     [ call (var "cast_obj") feature []
                     , str (typeName ++ "_" ++ feature ++ "(") .+ 
                       var "a_name" .+
                       str ")"
                     ]

-- Syntax building functions
p0 = attachEmptyPos

sType name = ClassType name []
block = p0 . Block
var = p0 . VarOrCall
callStmt trg str args = p0 (CallStmt $ call trg str args)
call trg str args = p0 (QualCall trg str args)
e1 .+ e2 = p0 (BinOpExpr Add e1 e2)
str = p0 . LitString
attached tMb e strMb = p0 (Attached tMb e strMb)
