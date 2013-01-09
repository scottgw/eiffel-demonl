{-# LANGUAGE OverloadedStrings #-}
module SerialGen (generateSerializer) where

import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.HashMap.Strict as Map
import qualified Data.Text as Text
import           Data.Text (Text)

import           Language.Eiffel.Parser
import qualified Language.Eiffel.PrettyPrint as PP
import           Language.Eiffel.Syntax
import           Language.Eiffel.Util
 
import           ClassEnv
import           EiffelBuilder

-- | Generate the serializer code given the template Eiffel class
-- the typing environment, and the queries to serialize (given as a map).
generateSerializer :: FilePath                -- ^ Template file path
                      -> FilePath             -- ^ Output file path
                      -> TInterEnv            -- ^ Typing environment
                      -> Map Typ (Set Text) -- ^ Map of features to serialize 
                      -> IO ()
generateSerializer inFile outFile env featMap = do
  clsEi <- parseClassFile inFile
  
  let
    cls' = 
      either (error $ "generateSerializer: couldn't parse: " ++ inFile)
             (addSerializerRoutine env featMap) 
             clsEi
  writeFile outFile (show $ PP.toDoc cls')

addSerializerRoutine :: TInterEnv -> Map Typ (Set Text) -> Clas -> Clas
addSerializerRoutine env featMap cls =
  addFeature cls (serializeRoutine env featMap)

serializeRoutine :: TInterEnv -> Map Typ (Set Text) -> Routine
serializeRoutine env featMap = 
    (emptyRoutine "serialize_")
        { routineArgs = [Decl "obj" anyType, Decl "name" (ClassType "STRING" [])]
        , routineImpl = RoutineBody [] [] (serializeMap env featMap)
        }

serializeMap :: TInterEnv -> Map Typ (Set Text) -> Stmt
serializeMap env featMap = ifs elseIfs
  where 
    elseIfs = map (uncurry (condAndStmt env)) (Map.toList featMap)
        
    condAndStmt  env type_ featNames =
      ( attached (Just $ genericToAny type_) obj (Just castObjStr)
      , do_ [serializeType env type_ featNames])


serializeType :: TInterEnv -> Typ -> Set Text -> Stmt
serializeType env type_ featNames = 
  do_ (map (serializeAttr env type_) (Set.toList featNames))

serializeAttr env type_ featName
  | isBasic resType  = serializeBasic type_ featName
  | otherwise        = serializeRef type_ featName resType
  where
    resType = featResult env type_ featName

serializeBasic type_ featName = 
  callStmt current "add_var" [strDmnCall, strValue]
  where
    strValue   = cast_obj .@ featName .< [] .@ "out" .< []
    strDmnCall = funcNameParen type_ featName
    
serializeRef type_ featName resType = 
  do_ [ callStmt current "serialize_ref" [ cast_obj .@ featName .< []
                                         , name
                                         , funcName type_ featName
                                         , eStr (classNameType resType)
                                         ]
      ]


funcName type_ featName = eStr (Text.concat [classNameType type_, "_", featName])
-- The unary function call as it would appear in demonL.
funcNameParen type_ featName =
  funcName type_ featName .+ eStr "(" .+ name .+ eStr ")"

cast_obj = var castObjStr
locals = var "locals"
refMap = var "refMap"
found  = var "found"
name   = var "name"
obj    = var "obj"
serial = var "serial"

castObjStr = "cast_obj"

genericToAny :: Typ -> Typ
genericToAny (ClassType s gs) = ClassType s (map (const anyType) gs)
genericToAny t = error $ "genericToAny: " ++ show t

featResult env t featName = resType
  where  
    Just class_ = envLookupType t env 
    Just feat   = findFeatureEx class_ featName
    resType     = featureResult feat
