{-# LANGUAGE ScopedTypeVariables #-}
module DomainGen where

import Data.List (nub)

import Data.Maybe

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Language.DemonL.AST as D

import Language.Eiffel.Syntax as E hiding (select)
import Language.Eiffel.Util
import Language.Eiffel.Position
import Language.Eiffel.TypeCheck.TypedExpr as T

import ClassEnv
import Domain
import Util
import SpecialSerialization


-- | Generate the minimal domain and also the extra instrumentation
-- class necessary for the nullary 
domain :: String 
          -> AbsClas (RoutineBody TExpr) TExpr 
          -> TInterEnv 
          -> (D.DomainU, Clas)
domain featureName clas flatEnv =
  (dom, extraInstrClass)
  where 
    Just rout = findFeature clas featureName

    pres :: [TExpr]
    pres = nub 
           (runInterfaceReader 
            (allPreConditions 
             (contents (routineBody (routineImpl rout)))) 
            flatEnv)
      
    typesAndNames :: [Set (Typ, Set String)]
    typesAndNames = map (domActions flatEnv) pres
    
    typeNameMap :: Map Typ (Set String)
    typeNameMap = collectNames (Set.unions typesAndNames)

    domainClasses = Map.mapWithKey (cutDownClass flatEnv) typeNameMap
      
    -- Include the generation of the EXTRA_INSTR class
    -- this should be based on the type-map where for each clas -> feature
    -- the feature is examined if it has no arguments, if so (and it is a 
    -- routine) then it goes into the EXTRA_INSTR.
      
    dom = makeDomain $ Map.elems domainClasses
    extraInstrClass = extraInstrs flatEnv typeNameMap
    

-------------------------------------
-- Implementy bits
--

data Indicator = Indicator Typ String deriving (Eq, Ord, Show)
indicatorTuple (Indicator t name) = (t, Set.singleton name)

data Action =
  Action { actionType :: Typ 
         , actionName :: String 
         } deriving (Eq, Ord, Show)

actionTuple (Action t name) = (t, Set.singleton name)

domActions :: TInterEnv -> T.TExpr -> Set (Typ, Set String)
domActions env e = 
  let eIndicators = exprIndicators e
      -- Desired interface:
      domActions' :: Set Indicator -> Set Action
      domActions' = Set.fold (Set.union . go) Set.empty
        where
          go :: Indicator -> Set Action
          go ind@(Indicator typ _name) = 
            let Just clas = envLookup (classNameType typ) env
                routs = allRoutines clas
                indicators = clausesIndicators . featurePost
                hasIndicator = Set.member ind . indicators
                modifyIndicators = filter hasIndicator routs
            in Set.fromList (map (\r -> Action typ (featureName r)) 
                                 modifyIndicators)
  in (Set.map indicatorTuple eIndicators) `Set.union` 
     (Set.map actionTuple (domActions' eIndicators))

clausesIndicators :: [Clause T.TExpr] -> Set Indicator
clausesIndicators = Set.unions . map (exprIndicators . clauseExpr)

exprIndicators :: T.TExpr -> Set Indicator
exprIndicators = go'
  where go' = go . contents
        go (T.Call trg name args _t) = 
          let argPairs = Set.unions (map exprIndicators (trg : args))
          in if isBasic (texpr trg) 
             then argPairs 
             else Set.insert (Indicator (texpr trg) name) argPairs
        go (T.EqExpr _ e1 e2) = go' e1 `Set.union` go' e2
        go _ = Set.empty


extraInstrs :: TInterEnv -> Map Typ (Set String) -> Clas
extraInstrs env = extractClass . Map.toList . onlyNullary 
  where
    -- only leave the nullary features
    onlyNullary = Map.mapWithKey (Set.filter . isNullary)
      
    -- does the feature of the type have no arguments?
    isNullary typ featureName = 
      let clas   = fromMaybe (error "extraInstrs: couldn't find type")
                             (envLookupType typ env)
          featMb = findFeature clas featureName
      in case featMb of
        Just feat -> null (routineArgs feat) && routineResult feat /= NoType
        Nothing   -> False

cutDownClass :: TInterEnv -> Typ -> Set String -> AbsClas EmptyBody TExpr
cutDownClass flatEnv typ names =
  let Just clas = envLookupType typ flatEnv
      featureNames  = map featureName (allFeatures clas :: [FeatureEx TExpr])
      undefineNames = Set.fromList featureNames Set.\\ names
  in Set.fold undefineName clas undefineNames
  
collectNames :: Set (Typ, Set String) -> Map Typ (Set String)
collectNames = Map.fromListWith Set.union . Set.toList 
