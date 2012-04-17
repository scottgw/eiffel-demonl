module ClassEnv where

import Data.Char
import qualified Data.Map as Map
import Data.Map (Map)

import Language.Eiffel.Syntax
import Language.Eiffel.Util (classNameType)
import Language.Eiffel.TypeCheck.Class
import Language.Eiffel.TypeCheck.TypedExpr as T
  
newtype ClassEnv body expr = ClassEnv (Map String (AbsClas body expr))
                           deriving Show

type TInterEnv = ClassEnv EmptyBody T.TExpr
type InterEnv = ClassEnv EmptyBody Expr

makeEnv :: [AbsClas body expr] -> ClassEnv body expr
makeEnv = ClassEnv . Map.fromList . map (\c -> (map toLower (className c), c))

-- |All keys' class-names in the class environment
envKeys :: ClassEnv body expr -> [String]
envKeys (ClassEnv m) = Map.keys m


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
    Nothing -> Map.lookup (map toLower name) m

envLookupType :: Typ -> ClassEnv body expr -> Maybe (AbsClas body expr)
envLookupType t = envLookup (classNameType t)
