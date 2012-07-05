module Util (allPreConditions, texprAssert', texprAssert, 
             Env (..), EnvReaderM, runEnvReader, 
             InterfaceReaderM, runInterfaceReader, liftToEnv,
             concatMapM) where

import Control.Monad.Trans.Reader
import Control.Monad.Trans
import Control.Monad.Identity

import Language.Eiffel.Syntax as E hiding (select)
import Language.Eiffel.Util
import Language.Eiffel.Position
import Language.Eiffel.TypeCheck.TypedExpr as T

import ClassEnv

-- | Basic environment holding the typed interface environment,
-- the current arguments, as well as the `Current` type.
data Env = Env
  { envInterfaces :: TInterEnv
  , envCurrent :: Typ
  , envArgs :: [Decl]
  }

-- | The reader monad with the underylying `Env`.
type EnvReaderM = ReaderT Env Identity

runEnvReader :: EnvReaderM a -> Env -> a
runEnvReader m r= runIdentity (runReaderT m r)


-- | A reader monad that only needs the typed interfaces of the classes.
type InterfaceReaderM = ReaderT TInterEnv Identity

-- | Run a 'InterfaceReaderM' given the typed interfaces.
runInterfaceReader :: InterfaceReaderM a -> TInterEnv -> a
runInterfaceReader m r = runIdentity (runReaderT m r)

-- | Lift the interface monad to the environment monad.
liftToEnv m = runInterfaceReader m `fmap` asks envInterfaces

allPreConditions :: UnPosTStmt -> InterfaceReaderM [T.TExpr]
allPreConditions = go
  where 
    pre  = texprAssert' featurePre

    go' :: TStmt -> InterfaceReaderM [T.TExpr]
    go' = go . contents

    go :: UnPosTStmt -> InterfaceReaderM [T.TExpr]
    go (Block blkBody) = concatMapM go' blkBody
    go (Assign _trg src) = pre src
    go (CallStmt e) = pre e
    go (Loop from untl _inv body _var) = do
      from' <- go' from
      untl' <- concatMapM (pre . clauseExpr) untl 
      body' <- go' body
      return (from' ++ untl' ++ body')      
    go e = error ("allPreConditions.go: " ++ show e)

-- | The monadic equivalent of the non-monadic list function.
concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat `liftM` mapM f xs

texprAssert' :: (FeatureEx TExpr -> [Clause TExpr]) 
                -> TExpr 
                -> InterfaceReaderM [T.TExpr]
texprAssert' select = go'
  where
    go' = go . contents
    go (T.Call trg name args _) = do
        callPreTExprs <- texprAssert select trg name
        rest <- concatMapM go' (trg : args)
        return (tNeqNull trg : rest ++ callPreTExprs)
    go (T.Access trg _ _) = (tNeqNull trg :) `liftM` go' trg
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
    go (T.Agent _ _ _ _) = error "preCond: unimplemented Agent"


readerLookup :: String -> InterfaceReaderM (Maybe (AbsClas EmptyBody TExpr))
readerLookup typeName = envLookup typeName `fmap` ask

texprAssert :: (FeatureEx TExpr -> [Clause TExpr]) 
            -> TExpr 
            -> String 
            -> InterfaceReaderM [T.TExpr]
texprAssert select targ name = do
  let ClassType typeName _ = texpr targ
  Just iface <- readerLookup typeName
  case findFeatureEx iface name of
    Just feat -> return $ map clauseExpr (select feat)
    Nothing -> error $ "texprPre: can't find feature: " ++ show targ ++ "." ++ name    

tNeqNull :: Pos UnPosTExpr -> T.TExpr
tNeqNull e = 
  let t = texpr e
      p = attachPos (position e)
  in p $ T.EqExpr T.Neq e (p $ T.LitVoid t)