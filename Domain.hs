{-# LANGUAGE OverloadedStrings #-}
module Domain where

import           Data.Either
import           Data.Maybe
import qualified Data.Text as Text
import           Data.Text (Text)

import           Language.Eiffel.Syntax as E
import           Language.Eiffel.Util as E
import           Language.Eiffel.Position
import           Language.Eiffel.TypeCheck.TypedExpr as T

import qualified Language.DemonL.TypeCheck as DT
import           Language.DemonL.AST as D
import           Language.DemonL.Types as D

makeDomain :: [AbsClas body TExpr] -> Domain DT.TExpr
makeDomain = foldr mergeDomains (Domain [] [] []) . map fromClass

mergeDomains :: Domain e -> Domain e -> Domain e
mergeDomains (Domain types1 procs1 funcs1) (Domain types2 procs2 funcs2) = 
    Domain (types1 ++ types2) (procs1 ++ procs2) (funcs1 ++ funcs2)

fromClass :: AbsClas body TExpr -> Domain DT.TExpr
fromClass clas =
    let
      typeName = className clas
      attrs    = map (fromAttr typeName) (allAttributes clas)
      struct   = Struct (Text.unpack typeName) []
      (prcds, funcs) = 
        partitionEithers $ map (fromRoutine clas) (allRoutines clas)
    in Domain [struct] prcds (attrs ++ funcs)

fromAttr :: Text -> Attribute TExpr -> Procedure DT.TExpr
fromAttr typeName attr = prcd
  where
    E.Decl name type_ = attrDecl attr
    prcd = Procedure (Text.unpack typeName ++ "_" ++ Text.unpack name)
                     [this (Text.unpack typeName)]
                     (fromType type_)
                     [] -- no pre or post conditions for an attribute
                     []

fromType :: E.Typ -> D.Type
fromType t | t == E.intType = D.IntType
           | t == E.boolType = D.BoolType
fromType (ClassType name _) = StructType (Text.unpack name) []
fromType E.NoType = D.NoType
fromType E.VoidType = StructType "NONE" []
fromType t = error $ "fromType: " ++ show t

fromDecl :: E.Decl -> D.Decl
fromDecl (E.Decl n t) = D.Decl (Text.unpack n) (fromType t)

this :: String -> D.Decl
this typeName = D.Decl "this" (StructType typeName [])

thisDecl :: AbsClas body exp -> D.Decl
thisDecl cls = this (Text.unpack $ className cls)

fromClause :: D.Type -> E.Clause TExpr -> D.Clause DT.TExpr
fromClause currType (E.Clause tagMb expr) = 
    let tag = fromMaybe "no_tag" tagMb
    in D.Clause (Text.unpack tag) (teToDCurr currType expr)

fromRoutine :: AbsClas body TExpr 
               -> AbsRoutine abs TExpr 
               -> Either (Procedure DT.TExpr) (Procedure DT.TExpr)
fromRoutine clas rtn = 
    let prcd = Procedure (Text.unpack (className clas) ++ "_" ++ Text.unpack (featureName rtn))
                         (thisDecl clas : map fromDecl (routineArgs rtn))
                         (fromType $ featureResult rtn)
                         (map fromClause' $ contractClauses $ routineReq rtn)
                         (map fromClause' $ contractClauses $ routineEns rtn)
        fromClause' = fromClause (fromType $ classToType clas)
    in case featureResult rtn of
         E.NoType -> Left prcd
         _ -> Right prcd

teToDCurr :: D.Type -> TExpr -> DT.TExpr
teToDCurr currType = teToD (DT.Var "this" currType)

teToD :: DT.TExpr -> TExpr -> DT.TExpr
teToD curr' te = go curr' (contents te)
  where
    go' curr = go curr . contents
    
    go :: DT.TExpr -> UnPosTExpr -> DT.TExpr
    go curr (T.Call trg name args t) = 
      let dtrg = go' curr trg
          ClassType cn _ = texpr trg
          expr = 
            DT.Call (Text.unpack cn ++ "_" ++ Text.unpack name) (dtrg : map (go' dtrg) args) (fromType t)
          withBinOp o = DT.BinOpExpr o dtrg (go' curr $ head args)
      in if length args == 1
         then case cn of
           "INTEGER_32" -> case name of
             "product" -> withBinOp DT.Mul IntType
             "plus"    -> withBinOp DT.Add IntType
             "minus"   -> withBinOp DT.Sub IntType
             "is_greater" -> withBinOp (DT.RelOp D.Gt IntType) BoolType
             _ -> error $ "teToD INTEGER_32: " ++ show expr
           "BOOLEAN" -> case name of
             "disjuncted"  -> withBinOp DT.Or BoolType
             "conjuncted"  -> withBinOp DT.And BoolType
             "implication" -> withBinOp DT.Implies BoolType
             _ -> error $ "teToD BOOLEAN: " ++ show expr
           _ -> expr
         else expr
    go curr (T.Access trg name t) = go curr (T.Call trg name [] t)
    go curr (T.EqExpr op e1 e2) = 
      DT.BinOpExpr (dEqOp op) (go' curr e1) (go' curr e2) BoolType
    go curr (T.Old e) = DT.UnOpExpr D.Old (go' curr e) (fromType (texpr e))
    go curr (T.CurrentVar _)         = curr
    go curr (T.Attached _ e _)       = 
      DT.BinOpExpr (DT.RelOp D.Neq BoolType) 
                   (go' curr e)
                   (DT.LitNull BoolType) 
                   BoolType
    go curr (T.Box _ e)     = go' curr e
    go curr (T.Unbox _ e)   = go' curr e
    go curr (T.Cast _ e)    = go' curr e
    go _curr (T.Var n t)     = DT.Var (Text.unpack n) (fromType t)
    go _curr (T.ResultVar t) = DT.ResultVar (fromType t) 
    go _curr (T.LitInt i)    = DT.LitInt i
    go _curr (T.LitBool b)   = DT.LitBool b
    go _curr (T.LitVoid t)   = DT.LitNull (fromType t)
    go _curr (T.LitChar _)   = error "teToD: unimplemented LitChar"
    go _curr (T.LitString _) = error "teToD: unimplemented LitString"
    go _curr (T.LitDouble _) = error "teToD: unimplemented LitDouble"
    go _curr (T.Agent _ _ _ _) = error "teToD: unimplemented Agent"
    go _curr (T.Tuple _)     = error "teToD: unimplemented Tuple"
    go _curr (T.LitArray _)  = error "teToD: unimplemented LitArray"
    go _curr (T.CreateExpr _ _ _) = error "teToD: unimplemented CreateExpr"
    go _curr (T.StaticCall _ _ _ _) = error "teToD: unimplemented StaticCall"
    go _curr (T.LitType _) = error "teToD: unimplemented LitType"

-- FIXME: Booltype below is probably wrong, but I can't recall using this
-- info here.
dEqOp o = DT.RelOp (rel o) BoolType
  where
    rel T.Eq = D.Eq
    rel T.Neq = D.Neq
    rel T.TildeEq = D.Eq
    rel T.TildeNeq = D.Neq

replaceExpr :: DT.TExpr -> DT.TExpr -> DT.TExpr -> DT.TExpr
replaceExpr new old = go
  where 
    rep = replaceExpr new old

    go e | e == old              = new
    go (DT.Call name args t)     = DT.Call name (map rep args) t
    go (DT.Access trg name t)    = DT.Access (rep trg) name t
    go (DT.BinOpExpr op e1 e2 t) = DT.BinOpExpr op (rep e1) (rep e2) t
    go (DT.UnOpExpr op e t)      = DT.UnOpExpr op (rep e) t
    go (DT.ResultVar t)          = 
      case old of
        DT.ResultVar t' -> error $ show (new, old, t)
        _ -> DT.ResultVar t
    go e = e


replaceExprNoOld :: DT.TExpr -> DT.TExpr -> DT.TExpr -> DT.TExpr
replaceExprNoOld new old = go
  where 
    rep = replaceExprNoOld new old
    go e | e == old           = new
    go (DT.Call name args t)     = DT.Call name (map rep args) t
    go (DT.Access trg name t)    = DT.Access (rep trg) name t
    go (DT.BinOpExpr op e1 e2 t) = DT.BinOpExpr op (rep e1) (rep e2) t
    go e@(DT.UnOpExpr D.Old _ t) = e
    go (DT.UnOpExpr op e t)      = DT.UnOpExpr op (rep e) t
    go e = e


-- op1 :: E.UnOp -> D.UnOp
-- op1 E.Not = D.Not
-- op1 E.Neg = D.Neg
-- op1 E.Old = D.Old
-- op1 E.Sqrt = error "teToD: unimpleneted Sqrt"

-- op2 :: E.BinOp -> D.BinOp
-- op2 E.Add = D.Add
-- op2 E.Sub = D.Sub
-- op2 E.Mul = D.Mul
-- op2 E.Div = D.Div
-- op2 E.Or  = D.Or
-- op2 E.And = D.And
-- op2 E.OrElse = D.Or
-- op2 E.AndThen = D.And
-- op2 E.Xor = D.RelOp D.Neq D.BoolType
-- op2 E.Implies = D.Implies
-- op2 (E.RelOp r _) = D.RelOp (rel r) D.NoType
-- op2 o = error ("op2: " ++ show o)

-- rel :: E.ROp -> D.ROp
-- rel E.Eq = D.Eq
-- rel E.Neq = D.Neq
-- rel E.Lte = D.Lte
-- rel E.Lt = D.Lt
-- rel E.Gt = D.Gt
-- rel E.Gte = D.Gte
-- rel E.TildeEq = D.Eq
-- rel E.TildeNeq = D.Neq
