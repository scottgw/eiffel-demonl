module ClassEnv where

import Data.Char
import qualified Data.Map as Map
import Data.Map (Map)

import Language.Eiffel.Syntax
import Language.Eiffel.TypeCheck.Class
import Language.Eiffel.TypeCheck.TypedExpr as T
     
newtype ClassEnv body expr = ClassEnv (Map String (AbsClas body expr))

type TInterEnv = ClassEnv EmptyBody T.TExpr
type InterEnv = ClassEnv EmptyBody Expr


makeEnv :: [AbsClas body expr] -> ClassEnv body expr
makeEnv = ClassEnv . Map.fromList . map (\c -> (map toLower (className c), c))


-- |Lookup a class name in the environment. This name should be lower-case,
-- and the function takes care of common type synonyms
-- (i.e., ``STRING'' as ``STRING_8'').
envLookup :: String -> ClassEnv body expr -> Maybe (AbsClas body expr)
envLookup name e@(ClassEnv m) = 
  let translate = [ ("string", "string_8")
                  , ("natural", "natural_32")
                  ]
  in case lookup name translate of
    Just alias -> Map.lookup alias m
    Nothing -> Map.lookup name m