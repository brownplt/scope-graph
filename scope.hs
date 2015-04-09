{-# LANGUAGE GADTs, Rank2Types #-}

module Scope (Env, Scope, emptyEnv,
              Decl, Refn, decl, refn, bind, find,
              FreshDecl (FreshDecl),
              Merged, merge, Scoped,
              
              emptyScope,
              
              clearEnv,
              
              leftEnv, rightEnv, makeLeftEnv, makeRightEnv,
              
              unhygienicDeclName, unhygienicRefnName) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Unique


type Name = String
type Id = Unique

data Decl a b = Decl Name Id
data Refn a = Refn Name

data Expt a = Expt Name Id
data Impt a = Impt Name

data FreshDecl = forall b. FreshDecl (forall a. Scoped a b (Decl a b))


decl :: String -> IO FreshDecl
decl name = do
  id <- newUnique
  return $ mkDecl name id

mkDecl :: String -> Id -> FreshDecl
mkDecl name id = FreshDecl $ \(Scope s) ->
  (Decl name id, Scope ((name, Just id) : s))

refn :: String -> Scope a -> Either BindError (Refn a)
refn name (Scope scope) =
  case lookup name scope of
    Nothing       -> Left  (UnboundError name)
    Just Nothing  -> Left  (AmbiguousError name)
    Just (Just _) -> Right (Refn name)

bind :: Decl a b -> v -> Env v a -> Env v b
bind (Decl name _) v (Env env) =
  Env (Map.insert name v env)

find :: Refn a -> Env v a -> v
find (Refn name) (Env env) = (Map.!) env name


{- Scope -}

newtype Scope a = Scope [(Name, Maybe Id)] -- nothing if binding is ambig
type Scoped a b t = Scope a -> (t, Scope b)

emptyScope :: Scope ()
emptyScope = Scope []

class Environment e where
  merge :: e a -> e b -> e (Merged a b)

instance Environment Scope where
  merge (Scope scope1) (Scope scope2) =
    let (suffix, diff1, diff2) = commonSuffix scope1 scope2 in
    let add (name, Nothing) = (name, Nothing)
        add (name, Just id) =
          case lookup name diff2 of
            Nothing -> (name, Just id)
            Just _  -> (name, Nothing) in
    Scope $ (map add diff1) ++ diff2 ++ suffix

data Merged a b

instance Environment (Env v) where
  merge (Env env1) (Env env2) = Env (Map.union env1 env2)


{- Environments -}
-- TODO: Make hygienic

data Env v a where
  Env :: Map Name v -> Env v a
  LeftEnv  :: Env v a -> Env v (Either a b)
  RightEnv :: Env v b -> Env v (Either a b)

--splitEnv :: Env v (Either a b) -> (Env v a, Env v b)

data Split a b

emptyEnv :: Env v ()
emptyEnv = Env (Map.empty)

clearEnv :: Env v a -> Env v ()
clearEnv (Env env) = Env env

leftEnv :: Env v (Either a b) -> Env v a
leftEnv (LeftEnv env) = env

rightEnv :: Env v (Either a b) -> Env v b
rightEnv (RightEnv env) = env

makeLeftEnv :: Env v a -> Env v (Either a b)
makeLeftEnv = LeftEnv

makeRightEnv :: Env v b -> Env v (Either a b)
makeRightEnv = RightEnv


{- Unhygienic Operations -}

unhygienicDeclName (Decl name _) = name
unhygienicRefnName (Refn name)   = name


{- Binding Errors -}

data BindError = UnboundError String
               | AmbiguousError String

instance Show BindError where
  show (UnboundError name)   = "Unbound identifier: " ++ name
  show (AmbiguousError name) = "Ambiguously bound identifier: " ++ name


{- Utility -}

commonPrefix :: Eq a => [a] -> [a] -> ([a], [a], [a])
commonPrefix (x:xs) (y:ys) =
  if x == y
  then let (zs, xs', ys') = commonSuffix xs ys in
  (x:zs, xs', ys')
  else ([], x:xs, y:ys)
commonPrefix xs ys = ([], xs, ys)

commonSuffix :: Eq a => [a] -> [a] -> ([a], [a], [a])
commonSuffix xs ys =
  let (a, b, c) = commonPrefix (reverse xs) (reverse ys) in
  (reverse a, reverse b, reverse c)
