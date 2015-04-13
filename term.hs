{-# LANGUAGE GADTs, Rank2Types #-}

module Term where

import Scope (Decl, Refn, FreshDecl (FreshDecl),
              Scope, Scoped, Env, Union, Join,
              emptyScope, union, joinEnv, splitEnv,
              unhygienicDeclName, unhygienicRefnName)
import qualified Scope as S
import Control.Monad (liftM, liftM2, liftM3)


data Term a b where
  {- Variables -}
  Decl :: Decl a b -> Term a b
  Refn :: Refn a   -> Term a a
  
  {- Magic -}
  Closed  :: Term () () -> Term a a
  RightT  :: Term b c -> Term (Join a b) (Join a c)
  LeftT   :: Term a b -> Term (Join a c) (Join b c)
  WrapCtx :: Term (Join () a) (Join c b) -> Term a b

  {- Core Language -}
  Apply  :: Term a a -> Term a a -> Term a a
  Lambda :: Term a b -> Term b b -> Term a a
  Param  :: Term a b -> Term a c -> Term a (Union b c)
  If     :: Term a a -> Term a a -> Term a a -> Term a a

  {- Syntactic Sugar -}
  Let :: Term a b -> Term a a -> Term b b -> Term a a
  Or  :: Term a a -> Term a a -> Term a a


{- Term & Context Construction -}

type STerm a b = Scoped a b (Term a b)

data Fresh = forall b. Fresh (forall a. STerm a b)

makeTerm :: Scoped () b (Term a b) -> IO (Term a b)
makeTerm t = return $ fst $ t $ emptyScope

type Ctx a b p q =
  Scope a -> (Term (Join a p) (Join b q), Scope b)

term :: STerm a b -> Ctx a b p p
term t a =
  let (t', b) = t a in
  (LeftT t', b)

hole :: Term p q -> Ctx a a p q
hole t a = (RightT t, a)

makeContext:: Ctx () b p q -> IO (Term p q)
makeContext t = return $ WrapCtx $ fst $ t emptyScope


decl :: String -> IO Fresh
decl name = do
  FreshDecl f <- S.decl name
  return $ Fresh $ \s -> let (d, s') = f s in (Decl d, s')

refn :: String -> forall a. STerm a a
refn name s =
  let t = case S.refn name s of
        Right r  -> Refn r
        Left err -> error $ show err in
  (t, s)

tParam ab ac s =
  let (b, sb) = ab s
      (c, sc) = ac s in
  (Param b c, union sb sc)

tApply  = S.runScoped2 Apply
tLambda = S.runScoped2 Lambda
tOr     = S.runScoped2 Or
tIf     = S.runScoped3 If

tLet x a b s =
  let (x', s') = x s
      (a', _)  = a s
      (b', _)  = b s' in
  (Let x' a' b', s)



subst :: Env (Maybe (Term () ())) a -> Term a b -> Term a b
subst env t = fst (sb env t) where
  sb :: Env (Maybe (Term () ())) a -> Term a b
        -> (Term a b, Env (Maybe (Term () ())) b)
  
  sb env (Decl d) = (Decl d, S.bind d Nothing env)
  sb env (Refn r) =
    let t = case S.find r env of
          Nothing -> Refn r
          Just t  -> Closed t in
    (t, env)
  
  sb env (Closed t) =
    let (t', env') = sb S.emptyEnv t in
    (Closed t', env)
  sb env (LeftT a) =
    let (envL, envR) = splitEnv env
        (a', envL') = sb envL a in
    (LeftT a', joinEnv envL' envR)
  sb env (RightT b) =
    let (envL, envR) = splitEnv env
        (b', envR') = sb envR b in
    (RightT b', joinEnv envL envR')  
  sb env (WrapCtx t) =
    let (t', env') = sb (joinEnv S.emptyEnv env) t in
    (WrapCtx t', snd $ splitEnv env')
  
  sb env (Lambda x b) =
    let (x', envx) = sb env x in
    (Lambda x' (subst envx b), env)
  sb env (Param a b) =
    let (a', enva) = sb env a
        (b', envb) = sb env b in
    (Param a' b', union enva envb)
  sb env (Let x a b) =
    let (x', envx) = sb env x
        (a', _)    = sb env a
        (b', _)    = sb envx b in
    (Let x' a' b', env)
  sb env (Apply a b) = (Apply (subst env a) (subst env b), env)
  sb env (If a b c)  = (If    (subst env a) (subst env b) (subst env c), env)
  sb env (Or a b)    = (Or    (subst env a) (subst env b), env)


unhygienicShowTerm :: Term a b -> String
unhygienicShowTerm t = sh t 0 where
  sh :: Term a b -> Int -> String
  sh t n = case t of
    Decl d     -> showVar (unhygienicDeclName d) n
    Refn r     -> showVar (unhygienicRefnName r) n
    
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


{- Exports -}

bind = S.bind
emptyEnv = S.emptyEnv
