{-# LANGUAGE GADTs, Rank2Types #-}

module Term where

import qualified Scope as S


data Term a b where
  Decl :: S.Decl a b -> Term a b
  Refn :: S.Refn a   -> Term a a
  
  Closed :: Term () () -> Term a a

  RightT :: Term b c -> Term (S.Split a b) (S.Split a c)
  LeftT  :: Term a b -> Term (S.Split a c) (S.Split b c)

  Apply :: Term a a -> Term a a -> Term a a
  Lambda :: Term a b -> Term b b -> Term a a
  Param :: Term a b -> Term a c -> Term a (S.Merged b c)
  If :: Term a a -> Term a a -> Term a a -> Term a a

  {- Sugar -}
  Let :: Term a b -> Term a a -> Term b b -> Term a a
  Or :: Term a b -> Term a b -> Term a b

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
  (Apply b c, sa)

lamb :: STerm a b -> STerm b b -> STerm a a
lamb ab bc sa =
  let (b, sb) = ab sa
      (c, _) = bc sb in
  (Lambda b c, sa)

tlet :: STerm a b -> STerm a a -> STerm b b -> STerm a a
tlet x a b s =
  let (x', s') = x s
      (a', _)  = a s
      (b', _)  = b s' in
  (Let x' a' b', s)

tor :: STerm a a -> STerm a a -> STerm a a
tor a b s =
  let (a', _) = a s
      (b', _) = b s in
  (Or a' b', s)

tif :: STerm a a -> STerm a a -> STerm a a -> STerm a a
tif a b c s =
  let ((a', _), (b', _), (c', _)) = (a s, b s, c s) in
  (If a' b' c', s)

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
subs env (Lambda a b) =
  let (a', env') = subs env  a
      (b', _)    = subs env' b in
  (Lambda a' b', env)
subs env (Apply a b) =
  let (a', env') = subs env a
      (b', _) = subs env' b in
  (Apply a' b', env)
subs env (RightT b) =
  let (envL, envR) = S.splitEnv env
      (b', envR') = subs envR b in
  (RightT b', S.joinEnv envL envR')
subs env (LeftT a) =
  let (envL, envR) = S.splitEnv env
      (a', envL') = subs envL a in
  (LeftT a', S.joinEnv envL' envR)


unhygienicShowTerm :: Term a b -> String
unhygienicShowTerm t =
  let sh :: Term a b -> String
      sh = unhygienicShowTerm in
  case t of
    Decl d   -> S.unhygienicDeclName d
    Refn r   -> S.unhygienicRefnName r
    Param a b -> sh a ++ " " ++ sh b
    Apply a b -> "(" ++ sh a ++ " " ++ sh b ++ ")"
    Lambda a b -> "(lam " ++ sh a ++ ". " ++ sh b ++ ")"
    Closed t -> sh t
