{-# LANGUAGE ScopedTypeVariables #-}
module DomainGen where

import Data.List (nub)

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import Language.DemonL.PrettyPrint

import Language.Eiffel.Syntax as E hiding (select)
import Language.Eiffel.Util
import Language.Eiffel.Position
import Language.Eiffel.TypeCheck.TypedExpr as T

import ClassEnv
import Domain
import Util

data Indicator = Indicator Typ String deriving (Eq, Ord, Show)
indicatorTuple (Indicator t name) = (t, name)

data Action = 
  Action { actionType :: Typ 
         , actionName :: String 
         } deriving (Eq, Ord, Show)

actionTuple (Action t name) = (t, name)

domActions :: TInterEnv -> T.TExpr -> Set (Typ, String)
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

domain :: String -> AbsClas (RoutineBody TExpr) TExpr -> TInterEnv -> IO ()
domain featureName clas flatEnv =
  let Just rout :: Maybe (AbsRoutine (RoutineBody TExpr) TExpr) = 
                    findFeature clas featureName

      pres :: [TExpr]
      pres = nub $ runInterfaceReader (allPreConditions $ contents $ routineBody (routineImpl rout)) flatEnv

      typesAndNames :: [Set (Typ, String)]
      typesAndNames = map (domActions flatEnv) pres

      typeNameMap :: Map Typ (Set String)
      typeNameMap = collectNames (Set.unions typesAndNames)

      domainClasses = Map.mapWithKey (cutDownClass flatEnv) typeNameMap
  in  print (domainDoc untypeExprDoc $ makeDomain $ Map.elems domainClasses)


cutDownClass :: TInterEnv -> Typ -> Set String -> AbsClas EmptyBody TExpr
cutDownClass flatEnv typ names =
  let Just clas = envLookupType typ flatEnv
      undefineNames = Set.fromList (map featureName (allFeatures clas :: [FeatureEx TExpr])) Set.\\ names
  in Set.fold undefineName clas undefineNames
  
collectNames :: Set (Typ, String) -> Map Typ (Set String)
collectNames = Set.fold go Map.empty
  where go (t, name) = 
          Map.insertWith (Set.union) t (Set.singleton name)
