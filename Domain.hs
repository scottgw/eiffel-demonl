module Domain where

import Data.Either
import Data.Maybe

import Language.Eiffel.Syntax as E
import Language.Eiffel.Util as E
import Language.Eiffel.Position
import Language.Eiffel.TypeCheck.TypedExpr as T

import Language.DemonL.AST as D
import Language.DemonL.Types as D

makeDomain :: [AbsClas body TExpr] -> Domain D.Expr
makeDomain = foldr mergeDomains (Domain [] [] []) . map fromClass

mergeDomains :: Domain e -> Domain e -> Domain e
mergeDomains (Domain types1 procs1 funcs1) (Domain types2 procs2 funcs2) = 
    Domain (types1 ++ types2) (procs1 ++ procs2) (funcs1 ++ funcs2)

fromClass :: AbsClas body TExpr -> DomainU
fromClass clas = 
    let attrs = map fromAttr (allAttributes clas)
        struct = Struct (className clas) attrs
        (prcds, funcs) = 
          partitionEithers $ map (fromRoutine clas) (allRoutines clas)
    in Domain [struct] prcds funcs

fromAttr :: Attribute TExpr -> D.Decl
fromAttr attr = fromDecl (attrDecl attr)

fromType :: E.Typ -> D.Type
fromType t | t == E.intType = D.IntType
fromType (ClassType name _) = StructType name []
fromType E.NoType = D.NoType
fromType t = error $ "fromType: " ++ show t

fromDecl :: E.Decl -> D.Decl
fromDecl (E.Decl n t) = D.Decl n (fromType t)

thisDecl :: AbsClas body exp -> D.Decl
thisDecl cls = D.Decl "this" (StructType (className cls) [])

fromClause :: E.Clause TExpr -> D.Clause D.Expr
fromClause (E.Clause tagMb expr) = 
    let tag = fromMaybe "no_tag" tagMb
    in D.Clause tag (teToDCurr expr)

fromRoutine :: AbsClas body TExpr -> AbsRoutine abs TExpr -> Either ProcedureU ProcedureU
fromRoutine clas rtn = 
    let prcd = Procedure (className clas ++ "_" ++ featureName rtn)
                         (thisDecl clas : map fromDecl (routineArgs rtn))
                         (fromType $ featureResult rtn)
                         (map fromClause $ contractClauses $ routineReq rtn)
                         (map fromClause $ contractClauses $ routineEns rtn)
    in case featureResult rtn of
         E.NoType -> Left prcd
         _ -> Right prcd

teToDCurr = teToD (D.Var "this")

teToD :: D.Expr -> TExpr -> D.Expr
teToD curr' te = go curr' (contents te)
  where
    go' curr = go curr . contents
    
    go :: D.Expr -> UnPosTExpr -> D.Expr
    go curr (T.Call trg name args _) = 
      let dtrg = go' curr trg
          ClassType cn _ = texpr trg
      in D.Call (cn ++ "_" ++ name) (dtrg : map (go' dtrg) args)
    go curr (T.Access trg name _)    = D.Access (go' curr trg) name
    go curr (T.EqExpr op e1 e2) = 
      D.BinOpExpr (dEqOp op) (go' curr e1) (go' curr e2)
    go curr (T.Old e) = D.UnOpExpr D.Old (go' curr e)
    go curr (T.CurrentVar _)         = curr
    go curr (T.Attached _ e _)       =
      let ClassType cn _ = texprTyp (contents e)
          structType = D.StructType cn []
      in D.BinOpExpr (D.RelOp D.Neq) (go' curr e) D.LitNull
    go curr (T.Box _ e)     = go' curr e
    go curr (T.Unbox _ e)   = go' curr e
    go curr (T.Cast _ e)    = go' curr e
    go _curr (T.Var n _)     = D.Var n
    go _curr (T.ResultVar _) = D.ResultVar
    go _curr (T.LitInt i)    = D.LitInt i
    go _curr (T.LitBool b)   = D.LitBool b
    go _curr (T.LitVoid _)   = D.LitNull
    go _curr (T.LitChar _)   = error "teToD: unimplemented LitChar"
    go _curr (T.LitString _) = error "teToD: unimplemented LitString"
    go _curr (T.LitDouble _) = error "teToD: unimplemented LitDouble"
    go _curr (T.Agent _ _ _ _) = error "teToD: unimplemented Agent"
    go _curr (T.Tuple _)     = error "teToD: unimplemented Tuple"
    go _curr (T.LitArray _)  = error "teToD: unimplemented LitArray"

dEqOp o = D.RelOp (rel o)
  where
    rel T.Eq = D.Eq
    rel T.Neq = D.Neq
    rel T.TildeEq = D.Eq
    rel T.TildeNeq = D.Neq

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
