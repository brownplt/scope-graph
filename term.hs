{-# LANGUAGE GADTs, Rank2Types #-}

module Term where

import qualified Scope as S


data Term a b where
  {- Variables -}
  Decl :: S.Decl a b -> Term a b
  Refn :: S.Refn a   -> Term a a
  
  {- Magic -}
  Closed  :: Term () () -> Term a a
  RightT  :: Term b c -> Term (S.Join a b) (S.Join a c)
  LeftT   :: Term a b -> Term (S.Join a c) (S.Join b c)
  WrapCtx :: Term (S.Join () a) (S.Join c b) -> Term a b

  {- Core Language -}
  Apply  :: Term a a -> Term a a -> Term a a
  Lambda :: Term a b -> Term b b -> Term a a
  Param  :: Term a b -> Term a c -> Term a (S.Union b c)
  If     :: Term a a -> Term a a -> Term a a -> Term a a

  {- Syntactic Sugar -}
  Let :: Term a b -> Term a a -> Term b b -> Term a a
  Or  :: Term a a -> Term a a -> Term a a

type Scoped a b t = Scope a -> (t, Scope b)

type STerm a b = Scoped a b (Term a b)

data Fresh = forall b. Fresh (forall a. STerm a b)


-- Neccesary?
scope :: Term a b -> Scope a -> Scope b
scope (Decl d)     = \(Scope a) -> Scope (S.scope d a)
scope (Refn _)     = id
scope (Closed t)   = id
scope (RightT t)   = \(Join a b) -> Join a (scope t b)
scope (LeftT t)    = \(Join a c) -> Join (scope t a) c
scope (WrapCtx t)  = \a ->
  snd $ splitScope $ scope t $ joinScope (Scope S.emptyScope) a
scope (Apply _ _)  = id
scope (Lambda _ _) = id
scope (Param p q)  = \a -> unionScope (scope p a) (scope q a)
scope (If a b c)   = id
scope (Let a b c)  = id
scope (Or a b)     = id

data Scope a where
  Scope :: S.Scope a -> Scope a
  Join  :: Scope a -> Scope b -> Scope (S.Join a b)

joinScope :: Scope a -> Scope b -> Scope (S.Join a b)
joinScope = Join

splitScope :: Scope (S.Join a b) -> (Scope a, Scope b)
splitScope (Join a b) = (a, b)

-- todo: What about union of Joined scopes?
unionScope :: Scope a -> Scope b -> Scope (S.Union a b)
unionScope (Scope a) (Scope b) = Scope (S.union a b)


makeTerm :: Scoped () b (Term a b) -> IO (Term a b)
makeTerm t = return $ fst $ t $ Scope S.emptyScope

makeScopedTerm :: Scoped () b (Term a b) -> IO (Term a b, Scope b)
makeScopedTerm t = return $ t $ Scope S.emptyScope

type Ctx a b p q =
  Scope a -> (Term (S.Join a p) (S.Join b q), Scope b)

tleft :: STerm a b -> Ctx a b p p
tleft t a =
  let (t', b) = t a in
  (LeftT t', b)
--tleft :: (STerm a b) -> STerm (S.Join a c) (S.Join b c)
{- tleft t ac =
  let (a, c)  = splitScope ac
      (t', b) = t a in
  (LeftT t', joinScope b c) -}

tright :: Term p q -> Ctx a a p q
tright t a = (RightT t, a)
--tright :: (STerm a b) -> STerm (S.Join c a) (S.Join c b)
{-tright t ca =
  let (c, a)  = splitScope ca
      (t', b) = t a in
  (RightT t', joinScope c b) -}

makeContext:: Ctx () b p q -> IO (Term p q)
makeContext t = return $ WrapCtx $ fst $ t (Scope S.emptyScope)


decl :: String -> IO Fresh
decl name = do
  S.FreshDecl f <- S.decl name
  return $ Fresh $ \(Scope s) -> let (d, s') = f s in (Decl d, Scope s')

refn :: String -> forall a. STerm a a
refn name (Scope s) =
  let t = case S.refn name s of
        Right r  -> Refn r
        Left err -> error $ show err in
  (t, Scope s)

--param :: STerm a b -> STerm a c -> STerm a (S.Union b c)
param ab ac s =
  let (b, sb) = ab s
      (c, sc) = ac s in
  (Param b c, unionScope sb sc)

--appl :: STerm a a -> STerm a a -> STerm a a
appl ab ac sa =
  let (b, _) = ab sa
      (c, _) = ac sa in
  (Apply b c, sa)

--lamb :: STerm a b -> STerm b b -> STerm a a
lamb ab bc sa =
  let (b, sb) = ab sa
      (c, _) = bc sb in
  (Lambda b c, sa)

--tlet :: STerm a b -> STerm a a -> STerm b b -> STerm a a
tlet x a b s =
  let (x', s') = x s
      (a', _)  = a s
      (b', _)  = b s' in
  (Let x' a' b', s)

--tor :: STerm a a -> STerm a a -> STerm a a
tor a b s =
  let (a', _) = a s
      (b', _) = b s in
  (Or a' b', s)

--tif :: STerm a a -> STerm a a -> STerm a a -> STerm a a
tif a b c s =
  let ((a', _), (b', _), (c', _)) = (a s, b s, c s) in
  (If a' b' c', s)


subs :: S.Env (Maybe (Term () ())) a -> Term a b
        -> (Term a b, S.Env (Maybe (Term () ())) b)
subs env t = sub env t where
  sub :: S.Env (Maybe (Term () ())) a -> Term a b
         -> (Term a b, S.Env (Maybe (Term () ())) b)
  sub env (Decl d) = (Decl d, S.bind d Nothing env)
  sub env (Refn r) =
    let t = case S.find r env of
          Nothing -> Refn r
          Just t  -> Closed t in
    (t, env)
  sub env (Closed t) =
    let (t', env') = sub (S.clearEnv env) t in
    (Closed t', env)
  sub env (LeftT a) =
    let (envL, envR) = S.splitEnv env
        (a', envL') = sub envL a in
    (LeftT a', S.joinEnv envL' envR)
  sub env (RightT b) =
    let (envL, envR) = S.splitEnv env
        (b', envR') = sub envR b in
    (RightT b', S.joinEnv envL envR')
  sub env (WrapCtx t) =
    let (t', env') = sub (S.joinEnv S.emptyEnv env) t in
    (WrapCtx t', snd $ S.splitEnv env')
  sub env (Lambda a b) =
    let (a', env') = sub env  a
        (b', _)    = sub env' b in
    (Lambda a' b', env)
  sub env (Apply a b) =
    let (a', env') = sub env a
        (b', _) = sub env' b in
    (Apply a' b', env)
  sub env (Param a b) =
    let (a', enva) = sub env a
        (b', envb) = sub env b in
    (Param a' b', S.union enva envb)
  sub env (If a b c) =
    let (a', _) = sub env a
        (b', _) = sub env b
        (c', _) = sub env c in
    (If a' b' c', env)
  sub env (Let x a b) =
    let (x', envx) = sub env x
        (a', _)    = sub env a
        (b', _)    = sub envx b in
    (Let x' a' b', env)
  sub env (Or a b) =
    let (a', _) = sub env a
        (b', _) = sub env b in
    (Or a' b', env)


unhygienicShowTerm :: Term a b -> String
unhygienicShowTerm t = sh t 0 where
  sh :: Term a b -> Int -> String
  sh t n = case t of
    Decl d     -> showVar (S.unhygienicDeclName d) n
    Refn r     -> showVar (S.unhygienicRefnName r) n
    
    -- ???
    LeftT t    -> sh t (n + 1)
    RightT t   -> sh t n
    Closed t   -> sh t n
    WrapCtx t  -> sh t n
    
    Param a b  -> sh a n ++ " " ++ sh b n
    Apply a b  -> "(" ++ sh a n ++ " " ++ sh b n ++ ")"
    Lambda a b -> "(lam " ++ sh a n ++ ". " ++ sh b n ++ ")"
    If a b c   -> "(if " ++ sh a n ++ " " ++ sh b n
                  ++ " " ++ sh c n ++ ")"

    Let x a b  -> "(let " ++ sh x n ++ " " ++ sh a n
                  ++ " " ++ sh b n ++ ")"
    Or a b     -> "(or " ++ sh a n ++ " " ++ sh b n ++ ")"

  showVar :: String -> Int -> String
  showVar name 0 = name
  showVar name n = name ++ "^" ++ show n