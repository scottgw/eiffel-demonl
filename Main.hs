module Main where

import Control.Applicative

import Data.Binary
import qualified Data.ByteString.Lazy as BS

import qualified Data.Map as Map

import Language.Eiffel.Parser.Parser
import Language.Eiffel.Syntax as E hiding (select)
import Language.Eiffel.Util
import Language.Eiffel.Position
import qualified Language.Eiffel.PrettyPrint as PP

import Language.Eiffel.TypeCheck.Class hiding (clas)
import Language.Eiffel.TypeCheck.Expr (flatten)
import Language.Eiffel.TypeCheck.Context
import Language.Eiffel.TypeCheck.TypedExpr as T

import System.Directory
import System.FilePath

import ClassEnv
import DepGen
import DomainGen
import GenerateSummaries
import InstrumentClass

workQueueFile = "work_queue.e"
testFile = "test.e"

regen = do
  genAllSummaries
  pwd <- getCurrentDirectory
  writeDomain $ pwd </> "test" </> testFile

getDomain file = do
  classEi <- parseClassFile file
  case classEi of
    Left err -> error $ "getDomain: " ++  show err
    Right cls -> do
      classInts <- Map.elems `fmap` readAllSummaries
      case depGen (makeEnv classInts) "test" of
        Left err -> error $ "getDomain: " ++ show err
        Right domainInts -> 
          case clasM classInts cls of 
            Left err -> error $ "getDomain: " ++  err
            Right tCls -> do
              tis <- typeInterfaces domainInts
              return (tis, tCls)


getDomainFile file = do 
  classEi <- parseClassFile file
  case classEi of
    Left err -> error $ "getDomain: " ++  show err
    Right cls -> do
      classInts <- Map.elems `fmap` readAllSummaries
      putStrLn "Read summaries"
      domainInts <- readDomain
      putStrLn "Read domain"
      case clasM classInts cls of 
        Left err -> error $ "getDomain: " ++  err
        Right tCls -> return (domainInts, tCls)

readDomain :: IO ([AbsClas EmptyBody T.TExpr])
readDomain = decode <$> BS.readFile "typed_domain.tdom"

writeDomain file = do
  (Right tis, _) <- getDomain file
  BS.writeFile "typed_domain.tdom" $ encode tis

main :: IO ()
main = do
  currDir <- getCurrentDirectory
  let testPath = currDir </> "test" </> testFile 
  (typedDomain, typedClass) <- getDomainFile testPath
  putStrLn "Typed"
  let flatEnv = flattenEnv $ makeEnv typedDomain
  print (PP.toDoc $ untype $ instrument flatEnv "test2" typedClass)
  domain "test2" typedClass flatEnv


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

