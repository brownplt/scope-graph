{-# LANGUAGE GADTs, Rank2Types #-}

module Scope (Decl, Refn, decl, refn, bind, find,
              scope,
              FreshDecl (FreshDecl),
              Join, Union, union,
              Env, EmptyEnv, emptyEnv, clearEnv, splitEnv, joinEnv,
              Scope, Scoped, emptyScope,
              unhygienicDeclName, unhygienicRefnName) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Unique


type Name = String
type Id = Unique

data Decl a b = Decl Name Id
data Refn a = Refn Name Id

data Expt a = Expt Name Id
data Impt a = Impt Name Id

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
    Nothing        -> Left  (UnboundError name)
    Just Nothing   -> Left  (AmbiguousError name)
    Just (Just id) -> Right (Refn name id)

bind :: Decl a b -> v -> Env v a -> Env v b
bind (Decl name id) v (Env env) =
  Env (Map.insert (name, id) v env)

find :: Refn a -> Env v a -> v
find (Refn name id) (Env env) = (Map.!) env (name, id)

scope :: Decl a b -> Scope a -> Scope b
scope _ (Scope scope) = Scope scope


{- Scope -}

newtype Scope a = Scope [(Name, Maybe Id)] -- nothing if binding is ambig
type Scoped a b t = Scope a -> (t, Scope b)

-- ??
emptyScope :: Scope ()
emptyScope = Scope []

class Environment e where
  union :: e a -> e b -> e (Union a b)

instance Environment Scope where
  union (Scope scope1) (Scope scope2) =
    let (suffix, diff1, diff2) = commonSuffix scope1 scope2 in
    let add (name, Nothing) = (name, Nothing)
        add (name, Just id) =
          case lookup name diff2 of
            Nothing -> (name, Just id)
            Just _  -> (name, Nothing) in
    Scope $ (map add diff1) ++ diff2 ++ suffix

data Union a b

instance Environment (Env v) where
  union (Env env1) (Env env2) = Env (Map.union env1 env2)


{- Environments -}
-- TODO: Make hygienic

newtype Env v a = Env (Map (Name, Id) v)

data Join a b

splitEnv :: Env v (Join a b) -> (Env v a, Env v b)
splitEnv (Env env) = (Env env, Env env)

joinEnv :: Env v a -> Env v b -> Env v (Join a b)
-- (guaranteed to be a disjoint union)
joinEnv (Env env1) (Env env2) = Env (Map.union env1 env2)

class EmptyEnv e

instance EmptyEnv ()

instance (EmptyEnv a, EmptyEnv b) => EmptyEnv (Join a b)

emptyEnv :: EmptyEnv e => Env v e
emptyEnv = Env (Map.empty)

clearEnv :: Env v a -> Env v ()
clearEnv (Env env) = Env env


{- Unhygienic Operations -}

unhygienicDeclName (Decl name _) = name
unhygienicRefnName (Refn name _) = name


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
