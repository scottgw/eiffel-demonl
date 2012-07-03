module Util (allPreConditions, texprAssert', texprAssert) where

import Language.Eiffel.Syntax as E hiding (select)
import Language.Eiffel.Util
import Language.Eiffel.Position
import Language.Eiffel.TypeCheck.TypedExpr as T

import ClassEnv

allPreConditions :: TInterEnv -> UnPosTStmt -> [T.TExpr]
allPreConditions env = go
  where 
    pre  = texprAssert' featurePre env
    go' = go . contents
    go :: UnPosTStmt -> [T.TExpr]
    go (Block blkBody) = concatMap go' blkBody
    go (Assign _trg src) = pre src
    go (CallStmt e) = pre e
    go (Loop from untl _inv body _var) =
      go' from ++ concatMap (pre . clauseExpr) untl ++ go' body
    go e = error ("allPreConditions.go: " ++ show e)


texprAssert' :: (FeatureEx TExpr -> [Clause TExpr]) 
                -> TInterEnv -> TExpr -> [T.TExpr]
texprAssert' select env = go'
  where
    go' = go . contents
    go (T.Call trg name args _) = 
      let callPreTExprs = texprAssert select env trg name
      in tNeqNull trg : concatMap go' (trg : args) ++ callPreTExprs
    go (T.Access trg _ _) = tNeqNull trg : go' trg
    go (T.Old e) = go' e
    go (T.CurrentVar _)      = []
    go (T.Attached _ e _)    = go' e
    go (T.Box _ e)     = go' e
    go (T.Unbox _ e)   = go' e
    go (T.Cast _ e)    = go' e
    go (T.Var _ _)     = []
    go (T.ResultVar _) = []
    go (T.LitInt _)    = []
    go (T.LitBool _)   = []
    go (T.LitVoid _)   = []
    go (T.LitChar _)   = error "preCond: unimplemented LitChar"
    go (T.LitString _) = error "preCond: unimplemented LitString"
    go (T.LitDouble _) = error "preCond: unimplemented LitDouble"
    go (T.LitArray _)  = error "preCond: unimplemented LitArray"
    go (T.Tuple _)     = error "preCond: unimplemented Tuple"
    go (T.Agent _ _ _ _) = error "preCond: unimplemented Agent"


texprAssert :: (FeatureEx TExpr -> [Clause TExpr]) 
            -> TInterEnv 
            -> TExpr 
            -> String 
            -> [T.TExpr]
texprAssert select env targ name = 
  let 
    ClassType typeName _ = texpr targ
    Just iface = envLookup typeName env
  in case findFeatureEx iface name of
    Just feat -> map clauseExpr (select feat)
    Nothing -> error $ "texprPre: can't find feature: " ++ show targ ++ "." ++ name    

tNeqNull :: Pos UnPosTExpr -> T.TExpr
tNeqNull e = 
  let t = texpr e
      p = attachPos (position e)
  in p $ T.EqExpr T.Neq e (p $ T.LitVoid t)
