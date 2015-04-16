{-# LANGUAGE GADTs, Rank2Types, MultiParamTypeClasses #-}

module Scope (Decl, Refn, newDecl, newRefn, bind, find,
              FreshDecl (FreshDecl),
              Scope, Scoped, emptyScope,
              Pair, Join, join,
              Env, emptyEnv, unpairEnv, pairEnv,
              Import, Export, newImport, newExport, inport, export,
              FreshExport (FreshExport), FreshImport (FreshImport),
              EnvState, joinState, emptyState, getState, setState,
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
data Import a b = Import Name Id

data FreshDecl =
  forall b. FreshDecl (forall a. Scoped a b (Decl a b))
data FreshExport =
  forall b. FreshExport (forall a. Scoped a b (Export a b))
data FreshImport =
  forall b. FreshImport (forall a. Scope a ->
                         Either BindError (Import a b, Scope b))


newDecl :: String -> IO FreshDecl
newDecl name = do
  id <- newUnique
  return $ FreshDecl $ \(Scope s) ->
    (Decl name id, Scope ((name, SBDecl id): s))

newRefn :: String -> Scope a -> Either BindError (Refn a)
newRefn name (Scope scope) =
  case lookup name scope of
    Nothing             -> Left  (UnboundError name)
    Just SBAmbig        -> Left  (AmbiguousError name)
    Just (SBExport _ _) -> Left  (BindingTypeError name)
    Just (SBDecl id)    -> Right (Refn name id)

newExport :: String -> IO FreshExport
newExport name = do
  id <- newUnique
  return $ FreshExport $ \s ->
    (Export name id, Scope [(name, SBExport id s)])

newImport :: String -> FreshImport
newImport name = FreshImport $ \(Scope scope) ->
  case lookup name scope of
    Nothing          -> Left (UnboundError name)
    Just SBAmbig     -> Left (AmbiguousError name)
    Just (SBDecl id) -> Left (BindingTypeError name)
    Just (SBExport id (Scope scope)) ->
      Right (Import name id, Scope scope)

bind :: EnvState s => Decl a b -> v -> Env v s a -> Env v s b
bind (Decl name id) v (Env st varEnv modEnv) =
  Env st (Map.insert (name, id) v varEnv) modEnv

find :: Refn a -> Env v s a -> v
find (Refn name id) (Env _ varEnv _) = (Map.!) varEnv (name, id)

export :: Export a b -> s -> Env v s a -> Env v s b
export (Export name id) st env =
  Env st Map.empty (Map.singleton (name, id) (castEnv env))

inport :: Import a b -> Env v s a -> Env v s b
inport (Import name id) (Env _ _ modEnv) =
  castEnv $ (Map.!) modEnv (name, id)


{- Scope -}

newtype Scope a = Scope [(Name, ScopeBinding)]

data ScopeBinding where
  SBAmbig  :: ScopeBinding
  SBExport :: Id -> Scope a -> ScopeBinding
  SBDecl   :: Id -> ScopeBinding

instance Eq ScopeBinding where
  SBAmbig == SBAmbig = True
  SBExport id1 (Scope s1) == SBExport id2 (Scope s2) =
    id1 == id2 && s1 == s2
  SBDecl id1 == SBDecl id2 = id1 == id2
  _ == _ = False

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


{- Join -}

class Joinable e where
  join :: e a -> e b -> e (Join a b)

data Join a b

instance Joinable Scope where
  -- todo: What about join of Paired scopes?
  join (Scope scope1) (Scope scope2) =
    let (suffix, diff1, diff2) = commonSuffix scope1 scope2 in
    let add (name, bind) =
          case lookup name diff2 of
            Nothing -> (name, bind)
            Just _  -> (name, SBAmbig) in
    Scope $ (map add diff1) ++ diff2 ++ suffix

instance EnvState s => Joinable (Env v s) where
  join (Env st1 varEnv1 modEnv1) (Env st2 varEnv2 modEnv2) =
    Env (joinState st1 st2) (Map.union varEnv1 varEnv2) (Map.union modEnv1 modEnv2)

class EnvState s where
  emptyState :: s
  joinState :: s -> s -> s


{- Environments -}

data Env v s a = Env s
                     (Map (Name, Id) v)
                     (forall b. (Map (Name, Id) (Env v s b)))

data Pair a b

getState :: Env v s a -> s
getState (Env s _ _) = s

setState :: Env v s a -> s -> Env v s a
setState (Env _ varEnv modEnv) st = Env st varEnv modEnv

unpairEnv :: Env v s (Pair a b) -> (Env v s a, Env v s b)
unpairEnv env = (castEnv env, castEnv env)

pairEnv :: EnvState s => Env v s a -> Env v s b -> s -> Env v s (Pair a b)
-- guaranteed to be a disjoint join:
pairEnv (Env _ varEnv1 modEnv1) (Env _ varEnv2 modEnv2) st =
  Env st (Map.union varEnv1 varEnv2) (Map.union modEnv1 modEnv2)

emptyEnv :: EnvState s => Env v s ()
emptyEnv = Env emptyState Map.empty Map.empty

castEnv :: Env v s a -> Env v s b
castEnv (Env st varEnv modEnv) = Env st varEnv modEnv


{- Unhygienic Operations -}

unhygienicDeclName (Decl name _) = name
unhygienicRefnName (Refn name _) = name


{- Binding Errors -}

data BindError = UnboundError String
               | AmbiguousError String
               | BindingTypeError String

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
