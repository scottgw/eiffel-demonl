module SpecialSerialization where

import Language.Eiffel.Syntax

import qualified Data.Set as Set
import Data.Set (Set)

import EiffelBuilder


type ExtractFeatures = (Typ, Set String)
                       
extractClass :: [ExtractFeatures] -> Clas
extractClass extrFeatures = addFeature base (extractProcess extrFeatures)
  where
    base = emptyClass "EXTRA_INSTR"

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
                     "serialize_attr"
                     [ call (var "cast_obj") feature []
                     , eStr (typeName ++ "_" ++ feature ++ "(") .+ 
                       var "a_name" .+
                       eStr ")"
                     ]
