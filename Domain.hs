module Domain where

import Data.Either

import Language.Eiffel.Eiffel as E
import Language.Eiffel.TypeCheck.TypedExpr as T

import Language.DemonL.AST as D
import Language.DemonL.Types as D

mergeDomains (Domain types1 procs1 funcs1) (Domain types2 procs2 funcs2) = 
    Domain (types1 ++ types2) (procs1 ++ procs2) (funcs1 ++ funcs2)

fromClass :: AbsClas body TExpr -> DomainU
fromClass clas = 
    let attrs = map fromAttr (allAttributes clas)
        struct = Struct (className clas) attrs
        (prcds, funcs) = partitionEithers $ map (fromRoutine clas) (allRoutines clas)
    in Domain [struct] prcds funcs

fromAttr :: Attribute TExpr -> D.Decl
fromAttr attr = fromDecl (attrDecl attr)

fromType :: E.Typ -> D.Type
fromType E.IntType = D.IntType
fromType (ClassType name _) = StructType name undefined

fromDecl :: E.Decl -> D.Decl
fromDecl (E.Decl n t) = D.Decl n (fromType t)

thisDecl :: AbsClas body exp -> D.Decl
thisDecl cls = D.Decl "this" (StructType (className cls) undefined)

fromClause :: E.Clause TExpr -> D.Clause D.Expr
fromClause (E.Clause tagMb expr) = 
    let tag = maybe "no_tag" id tagMb
    in D.Clause tag (teToD expr)

fromRoutine :: AbsClas body TExpr -> AbsRoutine abs TExpr -> Either ProcedureU ProcedureU
fromRoutine clas rtn = 
    let prcd = Procedure (featureName rtn)
                         (thisDecl clas : map fromDecl (routineArgs rtn))
                         (fromType $ featureResult rtn)
                         (map fromClause $ contractClauses $ routineReq rtn)
                         (map fromClause $ contractClauses $ routineEns rtn)
    in case featureResult rtn of
         E.NoType -> Left prcd
         _ -> Right prcd

teToD :: TExpr -> D.Expr
teToD te = go (contents te)
  where
    go (T.Call trg name args _) = D.Call name (teToD trg : map teToD args)
    go (T.Access trg name _)    = D.Access (teToD trg) name
    go (T.BinOpExpr op e1 e2 _) = D.BinOpExpr (op2 op) (teToD e1) (teToD e2)
    go (T.UnOpExpr op e _)      = D.UnOpExpr (op1 op) (teToD e)
    go (T.CurrentVar _)         = D.Var "this"
    go (T.Attached _ e _)       =
      let ClassType cn _ = texprTyp (contents e)
          structType = D.StructType cn []
      in D.BinOpExpr (D.RelOp D.Neq structType) (teToD e) D.LitNull
    go (T.Box _ e)     = teToD e
    go (T.Unbox _ e)   = teToD e
    go (T.Cast _ e)    = teToD e
    go (T.Var n _)     = D.Var n
    go (T.ResultVar _) = D.ResultVar
    go (T.LitInt i)    = D.LitInt i
    go (T.LitBool b)   = D.LitBool b
    go (T.LitVoid _)   = D.LitNull
    go (T.LitChar _)   = error "teToD: unimplemented LitChar"
    go (T.LitString _) = error "teToD: unimplemented LitString"
    go (T.LitDouble _) = error "teToD: unimplemented LitDouble"



op1 E.Not = D.Not
op1 E.Neg = D.Neg
op1 E.Old = D.Old
op1 E.Sqrt = error "teToD: unimpleneted Sqrt"

op2 E.Add = D.Add
op2 E.Sub = D.Sub
op2 E.Mul = D.Mul
op2 E.Div = D.Div
op2 E.Or  = D.Or
op2 E.And = D.And
op2 E.OrElse = D.Or
op2 E.AndThen = D.And
op2 E.Xor = D.RelOp D.Neq D.BoolType
op2 E.Implies = D.Implies
op2 (E.RelOp r _) = D.RelOp (rel r) D.NoType

rel E.Eq = D.Eq
rel E.Neq = D.Neq
rel E.Lte = D.Lte
rel E.Lt = D.Lt
rel E.Gt = D.Gt
rel E.Gte = D.Gte
rel E.TildeEq = D.Eq
rel E.TildeNeq = D.Neq
