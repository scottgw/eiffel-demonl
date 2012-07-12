module Instrument  where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans

import Data.List
import qualified Data.Set as Set
import Data.Set (Set)

import Language.Eiffel.Syntax as E hiding (select)
import Language.Eiffel.Util
import Language.Eiffel.Position

import Language.Eiffel.TypeCheck.TypedExpr as T

import qualified Language.DemonL.Types as D
import qualified Language.DemonL.AST as D
import Language.DemonL.PrettyPrint

import Domain
import Util

-- | The state monad built on the reader, with the list of assertions
-- for the weakest precondition.
type EnvM = StateT [D.Expr] EnvReaderM

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
    (E.ElseIfPart cond then_:es, elseMb) = go cif
   in p0 $ If cond then_ es elseMb
 

dand = D.BinOpExpr D.And
dnot = D.UnOpExpr D.Not
dimplies = D.BinOpExpr D.Implies

-- | The heart of the instrumentation of statements.
-- Given a statement, a new statement and a list of assertions
-- are returned.
-- The assertions are the weakest precondition calculations,
-- and the new statement has a call inserted before it that
-- goes to the demonic interference tool.
stmt' :: UnPosTStmt -> EnvM UnPosTStmt
stmt' = 
  let
    go :: UnPosTStmt -> EnvM UnPosTStmt
    go (Block blkBody) = do
      blkBody' <- mapM stmtM (reverse blkBody)
      return (Block $ reverse blkBody')
    go (Assign trg src) = do
      modify (\ ens -> replaceClause ens trg src)
      meldCall (Assign trg src)
   
    -- deal with condition preconditions
    go (If cond then_ elseParts elseMb) =
      let cif = convertCIf cond then_ elseParts elseMb
          ifImplies c e1 e2 = [dimplies c e1, dimplies (dnot c) e2]

          ifGo :: CIf -> EnvM CIf
          ifGo (CStmt s) = CStmt <$> stmtM s
          ifGo (CIf cCond cThen cElseMb) = do
            let condD = teToDCurr cCond
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
      let Call trg _ _ _ = contents e
      pre <- lift (liftToEnv $ preCond e)
      posts <- lift (liftToEnv $ texprAssert' featurePost e) -- ignores call chain
      newPre <- weakestPreCallM (dConj $ nub $ map teToDCurr posts) 
      put (pre ++ [newPre]) -- TODO: perform weakest precondition calculation
      meldCall (CallStmt e)
        
    -- TODO: Deal with until, invariant, and variant as well
    go (Loop from inv untl body var) = do 
      body' <- stmtM body
      from' <- stmtM from
      when (null inv) $ put []
      meldCall (Loop from' inv untl body' var)
    go e = error ("stmt'go: " ++ show e)
  in go

-- | Create weakest precondition expression from a function's postcondition.
-- The input postcondition should be preconverted to the DemonL expression
-- type, including using the correct 'Current' type, probably taken from
-- the originating target of the postcondition's call.
weakestPreCallM :: D.Expr -> EnvM D.Expr
weakestPreCallM post = weakestPreCall post <$> get

weakestPreCall :: D.Expr -> [D.Expr] -> D.Expr
weakestPreCall post qs = 
  let 
    nonOlds :: [D.Expr]
    nonOlds = reverse $ sortBy subExprOrd $ Set.toList $ nonConstExprs $ nonOldExprs post
      
    existName :: Integer -> String
    existName i = "ex__" ++ show i
    
    replaceUpdated :: D.Expr -> Integer -> D.Expr -> (Integer, D.Expr)
    replaceUpdated nonOldPart i inExpr = 
      let newExpr = replaceExprNoOld exName nonOldPart inExpr
          exName = D.Var (existName i)
      in (i + 1, newExpr) 
   
    useQuantVar :: Integer -> [D.Expr] -> D.Expr -> (Integer, [D.Expr]) 
    useQuantVar i exprs nonOld = mapAccumL (replaceUpdated nonOld) i exprs
    
    (n, post': qs') = foldl (uncurry useQuantVar) (0, post:qs) nonOlds
    
    postImpliesQs = D.BinOpExpr D.Implies (unOld post') (dConj qs')

    qvars = map (\name -> D.Decl name D.IntType) (Set.toList $ freeQVar postImpliesQs)

  in D.ForAll qvars postImpliesQs


unOld :: D.Expr -> D.Expr
unOld = go
  where
    go (D.Call name args) = D.Call name (map go args)
    go (D.BinOpExpr op e1 e2) = D.BinOpExpr op (go e1) (go e2)
    go (D.UnOpExpr D.Old e) = go e
    go (D.UnOpExpr o e) = D.UnOpExpr o (go e)
    go (D.ForAll ds e) = D.ForAll ds (go e)
    go e = e

-- | Get the free variables in an expression
freeQVar :: D.Expr -> Set String
freeQVar = go
  where
    go (D.Call _ args) = Set.unions (map go args)
    go (D.Var str) 
       | isQVar str = Set.singleton str
       | otherwise  = Set.empty
    go (D.BinOpExpr _ e1 e2) = Set.union (go e1) (go e2)
    go (D.UnOpExpr _ e) = go e
    go (D.ForAll ds e)  =
        let boundQVars = (filter isQVar . map D.declName) ds
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
nonOldExprs :: D.Expr -> Set D.Expr
nonOldExprs = 
  Set.filter (not .  isOld) . Set.filter (not . isVar) . properSubExprs

-- | Is the demonL expression 'Old'? 
isOld (D.UnOpExpr D.Old _) = True
isOld _ = False

-- | Is this a 'Var' AST node?
isVar :: D.Expr -> Bool
isVar (D.Var _) = True
isVar _ = False


nonConstExprs :: Set D.Expr -> Set D.Expr
nonConstExprs = 
 let isConst (D.LitInt _) = True
     isConst (D.LitNull) = True
     isConst (D.BinOpExpr _ _ _) = True
     isConst (D.UnOpExpr _ _) = True
     isConst _ = False
 in Set.filter (not . isConst)

-- | Proper subexpressions of a given expression.
-- This will surely break for cyclical ASTs.
properSubExprs :: D.Expr -> Set D.Expr
properSubExprs e = Set.delete e (subExprs e)

-- | All subexpressions of a given expression
subExprs :: D.Expr -> Set D.Expr
subExprs = go
  where
    go e@(D.Call _ args) = Set.insert e (Set.unions (map go args))
    go e@(D.BinOpExpr _ e1 e2) = Set.insert e (Set.union (go e1) (go e2))
    go e@(D.UnOpExpr _ subE) = Set.insert e (go subE)
    go e = Set.singleton e

-- | DemonL expression asserting that the given expression isn't null.
dNeqNull :: Pos UnPosTExpr -> D.Expr
dNeqNull e = D.BinOpExpr (D.RelOp D.Neq) (teToDCurr e) D.LitNull

-- | Conjunction of a list of DemonL assertions.
dConj :: [D.Expr] -> D.Expr
dConj [] = D.LitBool True
dConj es = foldr1 (D.BinOpExpr D.And) es

-- | Take an expression and accumulate all preconditions
-- and return them as DemonL expressions.
preCond :: TExpr -> InterfaceReaderM [D.Expr]
preCond = go . contents
  where
    go' = go . contents
    go (T.Call trg name args _) = do
      callPreTExpr <- texprAssert featurePre trg name
      let callPres = map (teToD (teToDCurr trg)) callPreTExpr
      rest <- concatMapM go' (trg : args)
      return (dNeqNull trg : rest ++ callPres)
    go (T.Access trg _ _) = (dNeqNull trg :) `fmap` go' trg
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

-- | Take a statement and make a new block with the accumulated
-- precondition (stored int the EnvM state) as a rely-call
-- first, then the argument statement.
meldCall :: UnPosTStmt -> EnvM UnPosTStmt
meldCall s = do
  pre <- get
  Env _ currType decls <- lift $ ask
  let 
    tuple x y = p0 $ T.Tuple [x, y]
    curr = p0 $ T.CurrentVar currType

    string :: String -> T.TExpr
    string name = p0 $ T.LitString name

    var name t = p0 $ T.Var name t

    array :: [T.TExpr] -> T.TExpr
    array = p0 . T.LitArray

    rely :: [T.TExpr] -> T.TExpr
    rely es = p0 $ T.Call curr "rely_call" es NoType

    precondStr = show $ untypeExprDoc $ dConj $ nub pre

    _agent = p0 . T.Agent

    declTup (Decl n t) = tuple (string n) (var n t)

    declArray :: T.TExpr
    declArray = 
      array (tuple (string "this") curr : map declTup decls)

    args :: [T.TExpr]
    args = [declArray, string precondStr]

    relyCall :: TStmt
    relyCall = p0 $ E.CallStmt $ rely args
  return (Block [relyCall, p0 s])


p0 :: a -> Pos a
p0 = attachEmptyPos

-- | Replace one expression with another in a list of DemonL
-- expressions.
replaceClause :: [D.Expr] -> TExpr -> TExpr -> [D.Expr]
replaceClause clauses old new = 
  map (replaceExpr (teToDCurr old) (teToDCurr new)) clauses  
