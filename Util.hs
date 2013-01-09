module Util (allPreConditions, texprAssert', texprAssert, 
             Env (..), EnvReaderM, runEnvReader, 
             InterfaceReaderM, runInterfaceReader, liftToEnv,
             concatMapM) where

import           Control.Applicative

import           Control.Monad.Trans.Reader
import           Control.Monad.Identity

import qualified Data.Text as Text
import           Data.Text (Text)

import qualified Language.DemonL.TypeCheck as DT

import           Language.Eiffel.Syntax as E hiding (select)
import           Language.Eiffel.Util
import           Language.Eiffel.Position
import           Language.Eiffel.TypeCheck.TypedExpr as T

import           ClassEnv

-- | Basic environment holding the typed interface environment,
-- the current arguments, as well as the `Current` type.
data Env = Env
  { envInterfaces :: TInterEnv
  , envRely    :: DT.TExpr
  , envCurrent :: Typ
  , envResult  :: Typ
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
liftToEnv m = runInterfaceReader m <$> asks envInterfaces

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
    go (If cond then_ elses elseMb) = do
      then' <- go' then_
      let elsePart (ElseIfPart c s) = (++) <$> pre c <*> go' s
      elses' <- concatMapM elsePart elses
      elseMb' <- maybe (return []) go' elseMb
      cond' <- pre cond
      return (cond' ++ then' ++ elses' ++ elseMb')
    go (Loop from untl _inv body _var) = do
      from' <- go' from
      untl' <- concatMapM (pre . clauseExpr) untl 
      body' <- go' body
      return (from' ++ untl' ++ body')      
    go e = error ("allPreConditions.go: " ++ show e)

-- | The monadic equivalent of the non-monadic list function.
concatMapM :: (Functor m, Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat <$> mapM f xs

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
    go (T.EqExpr _ e1 e2) = (++) <$> go' e1 <*> go' e2
    go (T.Access trg _ _) = (tNeqNull trg :) <$> go' trg
    go (T.Old e)          = go' e
    go (T.CurrentVar _)   = return []
    go (T.Attached _ e _) = go' e
    go (T.Box _ e)     = go' e
    go (T.Unbox _ e)   = go' e
    go (T.Cast _ e)    = go' e
    go (T.Var _ _)     = return []
    go (T.ResultVar _) = return []
    go (T.LitInt _)    = return []
    go (T.LitBool _)   = return []
    go (T.LitVoid _)   = return []
    go (T.LitChar _)   = error "texprAssert': unimplemented LitChar"
    go (T.LitString _) = error "texprAssert': unimplemented LitString"
    go (T.LitDouble _) = error "texprAssert': unimplemented LitDouble"
    go (T.LitArray _)  = error "texprAssert': unimplemented LitArray"
    go (T.Tuple _)     = error "texprAssert': unimplemented Tuple"
    go (T.Agent _ _ _ _) = error "texprAssert': unimplemented Agent"
    go e = error $ "texprAssert': unimplemented " ++ show e


replaceTExpr :: T.TExpr
                -> T.TExpr
                -> T.TExpr 
                -> T.TExpr
replaceTExpr replaceThis withThis inHere = go' inHere
  where
    go' :: T.TExpr -> T.TExpr
    go' = fmap go

    -- FIXME: Is we consider the untyped AST instead of the typed one.
    -- This is hacky, we only do it because the expressions may come from
    -- an uninstantiated generic class, and this will bypass that problem.
    --
    -- The real fix is to instantiate the other ASTs, but since it only affects
    -- generics (types) and we only care about AST shapes this should be OK.
    go e |
      (untypeExpr' $ contents replaceThis) == untypeExpr' e = contents withThis
    go (T.Call trg name args t) = 
      T.Call (go' trg) name (map go' args) t
    go (T.EqExpr op e1 e2) = T.EqExpr op (go' e1) (go' e2)
    go (T.Access trg name t) = T.Access (go' trg) name t
    go (T.Old e)          = T.Old (go' e)
    go (T.Attached as e t) = T.Attached as (go' e) t
    go (T.Box t e)     = T.Box t (go' e)
    go (T.Unbox t e)   = T.Unbox t (go' e)
    go (T.Cast t e)    = T.Cast t (go' e)
    go e = e

replaceCurrents :: T.TExpr -> T.TExpr -> [T.TExpr] -> [T.TExpr]
replaceCurrents oldCurr newCurr = map (replaceTExpr oldCurr newCurr)

-- readerLookup :: String -> InterfaceReaderM (Maybe (AbsClas EmptyBody TExpr))
-- readerLookup typeName = envLookup typeName <$> ask

readerLookup' :: Text -> InterfaceReaderM (AbsClas EmptyBody TExpr)
readerLookup' typeName = do
  e <- ask
  case envLookup typeName e of
    Nothing -> error $ "readerLookup': couldn't fine " ++ 
                        Text.unpack typeName ++ 
                        "\n environment: " ++ unlines (map Text.unpack $ envKeys e)
    Just c -> return c

texprAssert :: (FeatureEx TExpr -> [Clause TExpr]) 
            -> TExpr 
            -> Text
            -> InterfaceReaderM [T.TExpr]
texprAssert select targ name = do
  let t@(ClassType typeName _) = texpr targ
      oldCurr = fmap (const $ T.CurrentVar t) targ
      replace feat = 
        replaceCurrents oldCurr targ (map clauseExpr (select feat))
  iface <- readerLookup' typeName
  case findFeatureEx iface name of
    Just feat -> return $ replace feat
    Nothing -> error $ "texprPre: can't find feature: " ++ show targ ++ 
                       "." ++ Text.unpack name    

tNeqNull :: Pos UnPosTExpr -> T.TExpr
tNeqNull e = 
  let t = texpr e
      p = attachPos (position e)
  in p $ T.EqExpr T.Neq e (p $ T.LitVoid t)
