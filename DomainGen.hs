{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
module DomainGen (domain) where

import Data.List (nub)

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Language.DemonL.AST as D
import qualified Language.DemonL.TypeCheck as DT
import Language.Eiffel.Syntax as E hiding (select)
import qualified Language.Eiffel.Util as E
import Language.Eiffel.Position
import Language.Eiffel.TypeCheck.TypedExpr as T

import ClassEnv
import Domain
import Util

-- | Generate the minimal domain and also the extra instrumentation
-- class necessary for the nullary 
domain :: String 
          -> AbsClas (RoutineBody TExpr) TExpr 
          -> TInterEnv 
          -> (D.Domain DT.TExpr, Map Typ (Set String))
domain featureName clas flatEnv = (dom, onlyQueryMap)
  where       
    typeNameMap :: Map Typ (Set String)
    typeNameMap = Map.unionsWith Set.union $ map (domActions flatEnv) exprs
      where
        Just rout = E.findFeature clas featureName
        body = contents (routineBody (routineImpl rout))

        pres :: [TExpr]
        pres = nub (runInterfaceReader (allPreConditions body) flatEnv)
        
        contracts = map clauseExpr (contractClauses (routineEns rout)) ++ pres
        
        exprs = contracts ++ stmtExprs (routineBody (routineImpl rout))

    typeNameMapDummies = Map.filterWithKey (\ k v -> k /= NoType) $
                         Map.unionWith Set.union allArgMap typeNameMap
      where
        allArgMap = Map.fromList $ map (,Set.empty) (Set.toList allArgTypes)
        allArgTypes =
          Map.foldrWithKey 
            (\typ names -> Set.union (argTypes flatEnv typ names)) 
            Set.empty
            typeNameMap
    domainClasses = Map.mapWithKey (cutDownClass flatEnv) typeNameMapDummies

    onlyQueryMap = Map.mapWithKey (Set.filter . isQuery) typeNameMap
      where
        isQuery typ name = 
          E.featureResult (getFeatureEx flatEnv typ name) /= NoType

    dom = makeDomain $ Map.elems domainClasses
    

-------------------------------------
-- Implementy bits
--
stmtExprs :: TStmt -> [T.TExpr]
stmtExprs = go'
  where 
    goElsePart (ElseIfPart cond body) = cond : go' body
    
    go' = go . contents
    go (If cond then_ elseParts elseMb) = 
      cond : concat [ go' then_
                    , concatMap goElsePart elseParts
                    , maybe [] go' elseMb
                    ]
    go (Assign trg src) = [src]
    go (Block stmts)    = concatMap go' stmts
    go (CallStmt e)     = 
      case contents e of
        Call trg _ _ _ -> [trg]
    go (Loop from inv until body var) = 
      concat [ go' from
             , map clauseExpr inv
             , [until]
             , go' body
             , maybe [] (:[]) var
             ]
    go e = error (show e)

getFeatureEx env typ name = 
  maybe (error "getFeatureEx: no feature found") id (E.findFeatureEx c name)
  where
    c = envLookupType' typ env

-- | Take a class (type) and feature names and gather the set of
-- types used as arguments to the features.
argTypes :: TInterEnv -> Typ -> Set String -> Set Typ
argTypes env classTyp fnames = allFeatTypes
  where
    feats = map get (Set.toList fnames)
      where get = getFeatureEx env classTyp
    featTypes f = E.featureResult f : map declType (E.featureArgs f)
    allFeatTypes = 
      Set.unions (map (Set.fromList . featTypes) feats)


data Indicator = 
  Indicator Typ String Typ
  deriving (Eq, Ord, Show)

indicatorTuple (Indicator targ name _t) = (targ, Set.singleton name)

indicatorType (Indicator _ _ t) = t


data Action =
  Action { actionType :: Typ 
         , actionName :: String 
         } deriving (Eq, Ord, Show)

actionTuple (Action t name) = (t, Set.singleton name)

-- | Features which need to be included in the final domain.
domActions :: TInterEnv -> T.TExpr -> Map Typ (Set String)
domActions env e = 
  let indicators = exprIndicators e
      
      -- The set of actions (routines) which can modify the 
      -- set of indicators (queries)
      domActions' :: Set Indicator -> Set Action
      domActions' = Set.fold (Set.union . go) Set.empty
        where
          -- Which actions (procedures) mention the indicator in their
          -- postcondition.
          -- Basically: which procedures can change a query value.
          go :: Indicator -> Set Action
          go ind@(Indicator typ _name _resType) = 
            let Just clas = envLookup (E.classNameType typ) env
                routs = E.allRoutines clas
                inds = clausesIndicators . E.featurePost
                hasIndicator = Set.member ind . inds
                modifyIndicators = filter hasIndicator routs
            in Set.fromList (map (Action typ . E.featureName) modifyIndicators)
      

      fromSet :: (Ord k, Ord a) => Set (k, Set a) -> Map k (Set a)
      fromSet = Map.fromListWith Set.union . Set.toList
            
      queriesAndRoutines =  Map.unionWith Set.union
        (fromSet (Set.map indicatorTuple indicators))
        (fromSet (Set.map actionTuple (domActions' indicators)))
      
      -- Add relevant classes (ie, ones that are produced by queries)
      -- to the domain mapping. These definitions may be missed by 
      -- the actions or indicators directly, because they may not
      -- be mentioned in any pre or postcondition, but its easier to just
      -- generate the empty definitions in demonL in these cases.
      relevantClasses ind = 
        Map.insertWith Set.union (indicatorType ind) Set.empty
  in Set.foldr relevantClasses queriesAndRoutines indicators

clausesIndicators :: [Clause T.TExpr] -> Set Indicator
clausesIndicators = Set.unions . map (exprIndicators . clauseExpr)

exprIndicators :: T.TExpr -> Set Indicator
exprIndicators = go'
  where go' = go . contents

        go (T.Call trg name args t) = 
          if E.isBasic (texpr trg) 
          then argPairs
          else Set.insert (Indicator (texpr trg) name t) argPairs
          where argPairs = Set.unions (map exprIndicators (trg : args))
        go (T.Access trg name t) = Set.fromList [Indicator (texpr trg) name t]
        go (T.EqExpr _ e1 e2) = go' e1 `Set.union` go' e2
        go _ = Set.empty


cutDownClass :: TInterEnv -> Typ -> Set String -> AbsClas EmptyBody TExpr
cutDownClass flatEnv typ names =
  let clas = 
        maybe (E.makeGenericStub (Generic (E.classNameType typ) [] Nothing))
              id 
              (envLookupType typ flatEnv)
      featureNames  = map E.featureName 
                          (E.allFeatures clas :: [E.FeatureEx TExpr])
      undefineNames = Set.fromList featureNames Set.\\ names
  in Set.fold E.undefineName clas undefineNames