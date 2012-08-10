module Driver where

import Control.Applicative

import Data.Binary
import qualified Data.ByteString.Lazy as BS

import qualified Data.Map as Map

import Language.Eiffel.Parser.Parser
import Language.Eiffel.Syntax as E hiding (select)
import Language.Eiffel.Util
import Language.Eiffel.Position

import Language.Eiffel.TypeCheck.Class hiding (clas)
import Language.Eiffel.TypeCheck.Expr (flatten)
import Language.Eiffel.TypeCheck.Context
import Language.Eiffel.TypeCheck.TypedExpr as T

import System.Directory
import System.FilePath

import ClassEnv
import DepGen
import GenerateSummaries


-- | Used to regenerated the typed binary summaries. The summaries
-- make the startup time faster, but changes to class interfaces
-- require that they be regenerated.
regenHeader testClass testFile = do
  genAllSummaries
  pwd <- getCurrentDirectory
  writeDependencies testClass testFile

-- | For the given class file parse it and track down all
-- dependencies. Return the typed dependencies as well as
-- the typed class' AST.
getDepsAndClass testClass file = do
  classEi <- parseClassFile file
  case classEi of
    Left err -> error $ "getDomain: " ++  show err
    Right cls -> do
      classInts <- Map.elems `fmap` readAllSummaries
      case depGen (makeEnv classInts) testClass of
        Left err -> error $ "getDomain: " ++ show err
        Right dependentIFaces -> 
          case clasM classInts cls of 
            Left err -> error $ "getDomain: " ++  err
            Right tCls -> do
              tis <- typeInterfaces dependentIFaces
              return (tis, tCls)

-- | For the given class file read the pre-existing typed summaries
-- (this assumes that they have already been generated).
-- Return the loaded typed dependencies and the typed class AST.
loadDepsAndClass file = do
  classEi <- parseClassFile file
  case classEi of
    Left err -> error $ "getDomainFile: " ++  show err
    Right cls -> do
      classInts <- Map.elems `fmap` readAllSummaries
      putStrLn "Read summaries"
      domainInts <- readDependencies
      putStrLn "Read domain"
      case clasM classInts cls of 
        Left err -> error $ "getDomain: " ++  err
        Right tCls -> return (domainInts, tCls)


-- | Read the dependencies from the standard file.
readDependencies :: IO ([AbsClas EmptyBody T.TExpr])
readDependencies = decode <$> BS.readFile "typed_ifaces.tdeps"

writeDependencies testClass file = do
  (Right tis, _) <- getDepsAndClass testClass file
  BS.writeFile "typed_ifaces.tdeps" $ encode tis

block :: (t, [PosAbsStmt a]) -> (t, AbsStmt a)
block (cs, s) = (cs, Block s)

flattenEnv :: TInterEnv -> TInterEnv
flattenEnv (ClassEnv m) = 
  ClassEnv (Map.map (flatten' . classToType) m)
  where
    flatten' :: Typ -> AbsClas EmptyBody T.TExpr
    flatten' typ = 
      case idErrorRead (flatten typ) (mkCtx typ (Map.elems m)) of
        Left err -> error $ "flatten': " ++ err
        Right c -> classMapExprs updRoutine id id c
      where
        updRoutine r = r { routineReq = updContract (routineReq r)
                         , routineEns = updContract (routineEns r)
                         }
        updContract = mapContract (\cl -> cl {clauseExpr = go' (clauseExpr cl)})
        go' e = attachPos (position e) (go $ contents e)
        go (T.Call trg n args t) = T.Call (go' trg) n (map go' args) t
        go (T.EqExpr r e1 e2) = T.EqExpr r (go' e1) (go' e2)
        go (T.CurrentVar _t) = T.CurrentVar typ
        go e = e -- error $ "flattenEnv: " ++ show e