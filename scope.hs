{-# LANGUAGE GADTs, Rank2Types #-}

module Scope (Decl, Refn, decl, refn, bind, find,
              FreshDecl (FreshDecl),
              Scope, Scoped, emptyScope,
              Join, Union, union,
              Env, emptyEnv, splitEnv, joinEnv,
              runScoped1, runScoped2, runScoped3,
              unhygienicDeclName, unhygienicRefnName) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Unique
import Control.Category


type Name = String
type Id = Unique

data Decl a b = Decl Name Id
data Refn a = Refn Name Id

data Export a b = Export Name Id
data Import a = Import Name Id

data FreshDecl =
  forall b. FreshDecl (forall a. Scoped a b (Decl a b))
data FreshExport =
  forall b. FreshExport (forall a. Scoped a b (Export a b))


decl :: String -> IO FreshDecl
decl name = do
  id <- newUnique
  return $ FreshDecl $ \(Scope s) ->
    (Decl name id, Scope ((name, Just id): s))

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


{- Scope -}

newtype Scope a = Scope [(Name, Maybe Id)]

type Scoped a b t = Scope a -> (t, Scope b)

emptyScope :: Scope ()
emptyScope = Scope []

runScoped1 :: (t1 -> t2)
              -> Scoped a b t1
              -> Scoped a a t2
runScoped1 f ab a = let (t1, b) = ab a in (f t1, a)

runScoped2 :: (t1 -> t2 -> t3)
              -> Scoped a b t1
              -> Scoped b c t2
              -> Scoped a a t3
runScoped2 f ab bc a =
  let (t1, b) = ab a
      (t2, c) = bc b in
  (f t1 t2, a)

runScoped3 :: (t1 -> t2 -> t3 -> t4)
              -> Scoped a b t1
              -> Scoped b c t2
              -> Scoped c d t3
              -> Scoped a a t4
runScoped3 f ab bc cd a =
  let (t1, b) = ab a
      (t2, c) = bc b
      (t3, d) = cd c in
  (f t1 t2 t3, a)


{- Union -}

class Environment e where
  union :: e a -> e b -> e (Union a b)

data Union a b

instance Environment Scope where
  -- todo: What about union of Joined scopes?
  union (Scope scope1) (Scope scope2) =
    let (suffix, diff1, diff2) = commonSuffix scope1 scope2 in
    let add (name, Nothing) = (name, Nothing)
        add (name, Just id) =
          case lookup name diff2 of
            Nothing -> (name, Just id)
            Just _  -> (name, Nothing) in
    Scope $ (map add diff1) ++ diff2 ++ suffix

instance Environment (Env v) where
  union (Env env1) (Env env2) = Env (Map.union env1 env2)


{- Environments -}

newtype Env v a = Env (Map (Name, Id) v)

data Join a b

splitEnv :: Env v (Join a b) -> (Env v a, Env v b)
splitEnv (Env env) = (Env env, Env env)

joinEnv :: Env v a -> Env v b -> Env v (Join a b)
-- guaranteed to be a disjoint union:
joinEnv (Env env1) (Env env2) = Env (Map.union env1 env2)

emptyEnv :: Env v ()
emptyEnv = Env Map.empty


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
