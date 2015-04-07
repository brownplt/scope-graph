{-# LANGUAGE GADTs, Rank2Types #-}

module Scope (Env, Scope, merge, emptyEnv,
              Decl, Refn, decl, refn, bind, find,
              FreshDecl (FreshDecl), runScoped,
              
              Merged,
              leftEnv, rightEnv, makeLeftEnv, makeRightEnv,
              
              unhygienicDeclName, unhygienicRefnName) where

import Data.Map as Map
import Data.Map (Map)
import Control.Monad.State (State, get, put, evalState)


type Name = String
type Id = Int

data Decl a b = Decl Name Id
data Refn a = Refn Name

data Expt a = Expt Name Id
data Impt a = Impt Name

newtype Scope a = Scope (Map Name (Maybe Id))

data BindError = UnboundError String
               | AmbiguousError String

instance Show BindError where
  show (UnboundError name)   = "Unbound identifier: " ++ name
  show (AmbiguousError name) = "Ambiguously bound identifier: " ++ name

data FreshDecl a =
  FreshDecl (forall b. Scope a -> forall b. (Decl a b, Scope b))

--data FreshDecl a =
--  forall b. FreshDecl (Scope a -> (Decl a b, Scope b))


runScoped :: State Id (Scope a -> t) -> t
runScoped scoped = (evalState scoped 0) (Scope Map.empty)

decl :: String -> State Int (FreshDecl a)
decl name = do
  id <- get
  put (id + 1)
  return $ FreshDecl $ \(Scope s) ->
    (Decl name id, Scope (Map.insert name (Just id) s))

refn :: String -> Scope a -> Either BindError (Refn a)
refn name (Scope scope) =
  case Map.lookup name scope of
    Nothing        -> Left  (UnboundError name)
    Just Nothing   -> Left  (AmbiguousError name)
    Just (Just id) -> Right (Refn name)

bind :: Decl a b -> v -> Env v a -> Env v b
bind (Decl name _) v (Env env) =
  Env (Map.insert name v env)

find :: Refn a -> Env v a -> v
find (Refn name) (Env env) = (Map.!) env name

data Merged a b

class Environment e where
  merge :: e a -> e b -> e (Merged a b)

instance Environment (Env v) where
  merge (Env env1) (Env env2) = Env (Map.union env1 env2)

instance Environment Scope where
  merge (Scope scope1) (Scope scope2) =
    let joinBinds Nothing _ = Nothing
        joinBinds _ Nothing = Nothing
        joinBinds (Just id1) (Just id2) | id1 == id2 = Just id1
        joinBinds (Just id1) (Just id2) = Nothing in
    Scope (Map.unionWith joinBinds scope1 scope2)


-- TODO: Make hygienic

data Env v a where
  Env :: Map Name v -> Env v a
  LeftEnv  :: Env v a -> Env v (Either a b)
  RightEnv :: Env v b -> Env v (Either a b)

emptyEnv :: Env v ()
emptyEnv = Env Map.empty

--splitEnv :: Env v (Either a b) -> (Env v a, Env v b)

leftEnv :: Env v (Either a b) -> Env v a
leftEnv (LeftEnv env) = env

rightEnv :: Env v (Either a b) -> Env v b
rightEnv (RightEnv env) = env

--leftEnv :: Env v a -> Env v (Either a b)
--makeLeftEnv = LeftEnv

makeLeftEnv :: Env v a -> Env v (Either a b)
makeLeftEnv = LeftEnv

makeRightEnv :: Env v b -> Env v (Either a b)
makeRightEnv = RightEnv

{- Unhygienic Operations -}

unhygienicDeclName (Decl name _) = name
unhygienicRefnName (Refn name) = name


{- Is forall magic necessary for guarantees? -}

--withEmptyEnv :: (forall a. Env v a -> t) -> t
--withEmptyEnv f = f (Env Map.empty)

--withEmptyScope :: (forall a. Scope a -> t) -> t
--withEmptyScope f = f (Scope Map.empty)
