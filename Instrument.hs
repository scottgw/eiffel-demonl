{-# LANGUAGE OverloadedStrings #-}
module Instrument  where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Trans.Reader
import           Control.Monad.Trans.State
import           Control.Monad.Trans

import           Data.List
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Text as Text
import           Data.Text (Text)


import           Debug.Trace

import           Language.Eiffel.Syntax as E hiding (select)
import           Language.Eiffel.Util
import           Language.Eiffel.Position
import           Language.Eiffel.TypeCheck.TypedExpr as T

import qualified Language.DemonL.Types as D
import qualified Language.DemonL.TypeCheck as DT
import qualified Language.DemonL.AST as D
import           Language.DemonL.PrettyPrint

import           Domain
import           Util
import           EiffelBuilder

-- | The state monad built on the reader, with the list of assertions
-- for the weakest precondition.
type EnvM = StateT [DT.TExpr] EnvReaderM

-- C-like if AST, a simple conversion from the regular Eiffel AST one.

data CIf = CStmt T.TStmt
         | CIf T.TExpr T.TStmt (Maybe CIf)

convertCIf :: T.TExpr 
           -> T.TStmt 
           -> [E.ElseIfPart T.TExpr] 
           -> Maybe T.TStmt 
           -> CIf
convertCIf cond then_ [] elseMb = CIf cond then_ (fmap CStmt elseMb)
convertCIf cond then_ (E.ElseIfPart cond2 then2 : elseParts) elseMb = 
  CIf cond then_ (Just $ convertCIf cond2 then2 elseParts elseMb)

convertEIf :: CIf -> TStmt
convertEIf (CStmt s) = s
convertEIf cif =
  let 
    go (CIf c t eMb) =
      case eMb of
        Nothing -> ([E.ElseIfPart c t], Nothing)
        Just (CStmt s) -> ([E.ElseIfPart c t], Just s)
        Just cif' ->
          let (elses, elseMb') = go cif'
          in (E.ElseIfPart c t : elses, elseMb')
    go (CStmt _s) = ([],Nothing)
    (E.ElseIfPart cond then_:es, elseMb) = go cif
   in p0 $ If cond then_ es elseMb
 

dand e1 e2 = DT.BinOpExpr DT.And e1 e2 D.BoolType
dnot e = DT.UnOpExpr D.Not e D.BoolType
dimplies e1 e2 = DT.BinOpExpr DT.Implies e1 e2 D.BoolType

-- | The heart of the instrumentation of statements.
-- Given a statement, a new statement and a list of assertions
-- are returned.
-- The assertions are the weakest precondition calculations,
-- and the new statement has a call inserted before it that
-- goes to the demonic interference tool.
stmt' :: UnPosTStmt -> EnvM UnPosTStmt
stmt' e = do
  currT <- fromType <$>  envCurrent <$> lift ask
  let
    go :: UnPosTStmt -> EnvM UnPosTStmt
    go (Block blkBody) = do
      blkBody' <- mapM stmtM (reverse blkBody)
      return (Block $ reverse blkBody')
    go (Assign trg src) = do
      modify (replaceClause currT trg src)
      meldCall (Assign trg src)
   
    -- deal with condition preconditions
    go (If cond then_ elseParts elseMb) =
      let cif = convertCIf cond then_ elseParts elseMb
          ifImplies :: DT.TExpr -> DT.TExpr -> DT.TExpr -> [DT.TExpr]
          ifImplies c e1 e2 = [dimplies c e1, dimplies (dnot c) e2]

          ifGo :: CIf -> EnvM CIf
          ifGo (CStmt s) = CStmt <$> stmtM s
          ifGo (CIf cCond cThen cElseMb) = do
            let condD = teToDCurr currT cCond
            r <- get
            cThen' <- stmtM cThen
            r' <- get
            case cElseMb of
              Nothing -> do
                put (ifImplies condD (dConj r') (dConj r))
                return $ CIf cCond cThen' Nothing
              Just cElse -> do
                put r
                else_' <- ifGo cElse
                r'' <- get
                put (ifImplies condD (dConj r') (dConj r''))
                return $ CIf cCond cThen' (Just else_')
      in meldCall =<< contents <$> convertEIf <$> ifGo cif

    go (CallStmt e) = do
      preT <- lift (liftToEnv $ texprAssert' featurePre e) -- used to be: preCond currT e
      let pre = map (teToDCurr currT) preT
      posts <- lift (liftToEnv $ texprAssert' featurePost e) -- ignores call chain
      newPre <- weakestPreCallM (dConj $ nub $ map (teToDCurr currT) posts)
      put (pre ++ [newPre]) -- TODO: perform weakest precondition calculation
      meldCall (CallStmt e)
        
    -- TODO: Deal with until, invariant, and variant as well
    go (Loop from inv untl body vari) = do 
      body' <- stmtM body
      from' <- stmtM from
      when (null inv) $ put []
      meldCall (Loop from' inv untl body' vari)
    go e = error ("stmt'go: " ++ show e)
  go e

-- | Create weakest precondition expression from a function's postcondition.
-- The input postcondition should be preconverted to the DemonL expression
-- type, including using the correct 'Current' type, probably taken from
-- the originating target of the postcondition's call.
weakestPreCallM :: DT.TExpr -> EnvM DT.TExpr
weakestPreCallM post = weakestPreCall post <$> get

weakestPreCall :: DT.TExpr -> [DT.TExpr] -> DT.TExpr
weakestPreCall post qs = 
  let 
    nonOlds :: [DT.TExpr]
    nonOlds = reverse $ sortBy subExprOrd $ Set.toList $ nonConstExprs $ nonOldExprs post
      
    existName :: Integer -> String
    existName i = "ex__" ++ show i
    
    replaceUpdated :: DT.TExpr -> Integer -> DT.TExpr -> (Integer, DT.TExpr)
    replaceUpdated nonOldPart i inExpr = 
      let newExpr = replaceExprNoOld exName nonOldPart inExpr
          exName = DT.Var (existName i) (DT.texprType nonOldPart)
      in (i + 1, newExpr)
   
    useQuantVar :: Integer -> [DT.TExpr] -> DT.TExpr -> (Integer, [DT.TExpr]) 
    useQuantVar i exprs nonOld = mapAccumL (replaceUpdated nonOld) i exprs
    
    (_n, post': qs') = foldl (uncurry useQuantVar) (0, post:qs) nonOlds
    
    postImpliesQs = DT.BinOpExpr DT.Implies (unOld post') (dConj qs') D.BoolType

    qvars = map (uncurry D.Decl) (Set.toList $ freeQVar postImpliesQs)

  in DT.ForAll qvars postImpliesQs


unOld :: DT.TExpr -> DT.TExpr
unOld = go
  where
    go (DT.Call name args t) = DT.Call name (map go args) t
    go (DT.BinOpExpr op e1 e2 t) = DT.BinOpExpr op (go e1) (go e2) t
    go (DT.UnOpExpr D.Old e t) = go e
    go (DT.UnOpExpr o e t) = DT.UnOpExpr o (go e) t
    go (DT.ForAll ds e) = DT.ForAll ds (go e)
    go e = e

-- | Get the free variables in an expression
freeQVar :: DT.TExpr -> Set (String, D.Type)
freeQVar = go
  where
    go (DT.Call _ args t) = Set.unions (map go args)
    go (DT.Var str t) 
       | isQVar str = Set.singleton (str, t)
       | otherwise  = Set.empty
    go (DT.BinOpExpr _ e1 e2 t) = Set.union (go e1) (go e2)
    go (DT.UnOpExpr _ e t) = go e
    go (DT.ForAll ds e)  =
        let boundQVars = 
              filter ( \(n,t) -> isQVar n) $ map (\ (D.Decl n t) -> (n, t)) ds
        in Set.difference (go e) (Set.fromList boundQVars)
    go _ = Set.empty

-- Is quantified variable name?
isQVar :: String -> Bool
isQVar str = "ex__" `isPrefixOf` str

-- Ordering based on subexpressions.
subExprOrd e1 e2
  | Set.member e1 (properSubExprs e2) = LT
  | Set.member e2 (properSubExprs e1) = GT
  | otherwise = compare e1 e2

-- | Prefix a statement with a call to demonL with the weakest precondition.
stmtM :: TStmt -> EnvM TStmt
stmtM s = do
  s' <- stmt' (contents s)
  return (attachEmptyPos s')

-- | Gather the subexpressions of a given expression that are non-old.
-- 
-- This may be used to approximate the things that may have changed
-- as specificed by a postcondition.
nonOldExprs :: DT.TExpr -> Set DT.TExpr
nonOldExprs = 
  Set.filter (not .  isOld) . Set.filter (not . isVar) . properSubExprs

-- | Is the demonL expression 'Old'? 
isOld (DT.UnOpExpr D.Old _ _) = True
isOld _ = False

-- | Is this a 'Var' AST node?
isVar :: DT.TExpr -> Bool
isVar (DT.Var _ _) = True
isVar _ = False


nonConstExprs :: Set DT.TExpr -> Set DT.TExpr
nonConstExprs = 
 let isConst (DT.LitInt _) = True
     isConst (DT.LitNull _) = True
     isConst (DT.BinOpExpr _ _ _ _) = True
     isConst (DT.UnOpExpr _ _ _) = True
     isConst _ = False
 in Set.filter (not . isConst)

-- | Proper subexpressions of a given expression.
-- This will surely break for cyclical ASTs.
properSubExprs :: DT.TExpr -> Set DT.TExpr
properSubExprs e = Set.delete e (subExprs e)

-- | All subexpressions of a given expression
subExprs :: DT.TExpr -> Set DT.TExpr
subExprs = go
  where
    go e@(DT.Call _ args t) = Set.insert e (Set.unions (map go args))
    go e@(DT.BinOpExpr _ e1 e2 t) = Set.insert e (Set.union (go e1) (go e2))
    go e@(DT.UnOpExpr _ subE t) = Set.insert e (go subE)
    go e = Set.singleton e

-- | DemonL expression asserting that the given expression isn't null.
dNeqNull :: D.Type -> Pos UnPosTExpr -> DT.TExpr
dNeqNull currT e  
  | isBasic (texpr e) = DT.LitBool True
  | otherwise = DT.BinOpExpr (DT.RelOp D.Neq t)
                             (teToDCurr currT e) 
                             (DT.LitNull t)
                             D.BoolType
  where t = fromType (T.texpr e)

-- | Conjunction of a list of DemonL assertions.
dConj :: [DT.TExpr] -> DT.TExpr
dConj [] = DT.LitBool True
dConj es = foldr1 dand es

-- | Take an expression and accumulate all preconditions
-- and return them as DemonL expressions.
preCond :: D.Type -> TExpr -> InterfaceReaderM [DT.TExpr]
preCond currT = go . contents
  where
    go' = go . contents
    go (T.Call trg name args _) = do
      callPreTExpr <- texprAssert featurePre trg name
      let callPres = map (teToD (teToDCurr currT trg)) callPreTExpr
      rest <- concatMapM go' (trg : args)
      return (dNeqNull currT trg : rest ++ callPres)
    go (T.Access trg _ _) = (dNeqNull currT trg :) `fmap` go' trg
    go (T.Old e) = go' e
    go (T.CurrentVar _)      = return []
    go (T.Attached _ e _)    = go' e
    go (T.Box _ e)     = go' e
    go (T.Unbox _ e)   = go' e
    go (T.Cast _ e)    = go' e
    go (T.Var _ _)     = return []
    go (T.ResultVar _) = return []
    go (T.LitInt _)    = return []
    go (T.LitBool _)   = return []
    go (T.LitVoid _)   = return []
    go (T.LitChar _)   = error "preCond: unimplemented LitChar"
    go (T.LitString _) = error "preCond: unimplemented LitString"
    go (T.LitDouble _) = error "preCond: unimplemented LitDouble"
    go (T.LitArray _)  = error "preCond: unimplemented LitArray"
    go (T.Tuple _)     = error "preCond: unimplemented Tuple"
    go (T.Agent {}) = error "preCond: unimplemented Agent"
    go te           = error $ "preCond: unimplemented " ++ show te

-- | Take a statement and make a new block with the accumulated
-- precondition (stored int the EnvM state) as a rely-call
-- first, then the argument statement.
meldCall :: UnPosTStmt -> EnvM UnPosTStmt
meldCall s = do
  pre <- get
  
  Env _ rely currType resultType decls <- lift $ ask
  let
    curr = currVarT currType
  
    relyCall :: [T.TExpr] -> T.TExpr
    relyCall es = p0 $ T.Call curr "rely_call" es NoType

    preNoResult = map removeResult pre
    precondStr = Text.pack $ show $ typeExprDoc $ dConj $ nub preNoResult
    relyStr    = Text.pack $ show $ typeExprDoc rely

    serializer = p0 $ T.CreateExpr (ClassType "SERIALIZER" []) "reset" []

    declTup (Decl n t) = tupleT [ stringT n
                                , typeString t
                                , varT n t
                                ]

    typeString = stringT . classNameType
    result = p0 $ T.ResultVar resultType
  
    declArray :: T.TExpr
    declArray = 
      arrayT (tupleT [stringT "this", typeString currType, curr] : 
              tupleT [stringT "res", typeString resultType, result] : 
              map declTup decls)

    args :: [T.TExpr]
    args = [ p0 $ T.LitInt 0
           , declArray
           , stringT precondStr
           , stringT relyStr
           , serializer
           ]

    relyCall' :: TStmt
    relyCall' = p0 $ E.CallStmt $ relyCall args
  return (Block [relyCall', p0 s])


removeResult :: DT.TExpr -> DT.TExpr
removeResult withResult = go withResult
  where
    go (DT.Call name args t)     = DT.Call name (map go args) t
    go (DT.Access trg name t)    = DT.Access (go trg) name t
    go (DT.BinOpExpr op e1 e2 t) = DT.BinOpExpr op (go e1) (go e2) t
    go (DT.UnOpExpr op e t)      = DT.UnOpExpr op (go e) t
    go (DT.ForAll dcls e)        = DT.ForAll dcls (go e)
    go (DT.ResultVar t)          = DT.Var "res" t
    go e = e


-- | Replace one expression with another in a list of DemonL
-- expressions.
replaceClause :: D.Type -> TExpr -> TExpr -> [DT.TExpr] -> [DT.TExpr]
replaceClause currT old new = 
  map (replaceExpr  (teToDCurr currT new) (teToDCurr currT old))
