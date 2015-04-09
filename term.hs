{-# LANGUAGE GADTs, Rank2Types #-}

module Term where

import qualified Scope as S
import Control.Monad.State (State)
import Control.Monad (liftM)


data Term a b where
  Decl :: S.Decl a b -> Term a b
  Refn :: S.Refn a   -> Term a a
  
  Closed :: Term () () -> Term a a

  RightT :: Term b c -> Term (Either a b) (Either a c)
  LeftT  :: Term a b -> Term (Either a c) (Either b c)

  Appl :: Term a a -> Term a a -> Term a a
  Lamb :: Term a b -> Term b c -> Term a a
  Param :: Term a b -> Term a c -> Term a (S.Merged b c)

type STerm a b = S.Scoped a b (Term a b)

data FreshDecl = forall b. FreshDecl (forall a. STerm a b)


makeTerm :: (S.Scope () -> (Term () b, S.Scope b)) -> IO (Term () b)
makeTerm t = return (fst (t S.emptyScope))

decl :: String -> IO FreshDecl
decl name = do
  S.FreshDecl f <- S.decl name
  return $ FreshDecl $ \s -> let (d, s') = f s in (Decl d, s')

refn :: String -> forall a. STerm a a
refn name s =
  let t = case S.refn name s of
        Right r  -> Refn r
        Left err -> error $ show err in
  (t, s)

param :: STerm a b -> STerm a c -> STerm a (S.Merged b c)
param ab ac s =
  let (b, sb) = ab s
      (c, sc) = ac s in
  (Param b c, S.merge sb sc)

appl :: STerm a a -> STerm a a -> STerm a a
appl ab ac sa =
  let (b, _) = ab sa
      (c, _) = ac sa in
  (Appl b c, sa)

lamb :: STerm a b -> STerm b c -> STerm a a
lamb ab bc sa =
  let (b, sb) = ab sa
      (c, _) = bc sb in
  (Lamb b c, sa)


subs :: S.Env (Maybe (Term () ())) a -> Term a b
               -> (Term a b, S.Env (Maybe (Term () ())) b)
subs env (Decl d) = (Decl d, S.bind d Nothing env)
subs env (Refn r) =
  let t = case S.find r env of
        Nothing -> Refn r
        Just t  -> Closed t in
  (t, env)
subs env (Closed t) =
  let (t', env') = subs (S.clearEnv env) t in
  (Closed t', env)
subs env (Lamb a b) =
  let (a', env') = subs env  a
      (b', _)    = subs env' b in
  (Lamb a' b', env)
subs env (Appl a b) =
  let (a', env') = subs env a
      (b', _) = subs env' b in
  (Appl a' b', env)
subs env (RightT b) =
  let (b', env') = subs (S.rightEnv env) b in
  (RightT b', S.makeRightEnv env')
subs env (LeftT a) =
  let (a', env') = subs (S.leftEnv env) a in
  (LeftT a', S.makeLeftEnv env')


unhygienicShowTerm :: Term a b -> String
unhygienicShowTerm t =
  let sh :: Term a b -> String
      sh = unhygienicShowTerm in
  case t of
    Decl d   -> S.unhygienicDeclName d
    Refn r   -> S.unhygienicRefnName r
    Param a b -> sh a ++ " " ++ sh b
    Appl a b -> "(" ++ sh a ++ " " ++ sh b ++ ")"
    Lamb a b -> "(lam " ++ sh a ++ ". " ++ sh b ++ ")"
    Closed t -> sh t
