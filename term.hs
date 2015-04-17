{-# LANGUAGE GADTs, Rank2Types, FlexibleInstances, ScopedTypeVariables #-}

module Term where

import Data.Char (ord, chr)

import Scope hiding (bind, find, emptyEnv,
                     FreshImport (FreshImport), FreshExport (FreshExport))
import qualified Scope as S
import Interp

bind :: S.Decl a b -> v -> Env v s a -> Env v s b
bind = S.bind

find :: S.Refn a -> Env v s a -> v
find = S.find

emptyEnv :: s -> Env v s ()
emptyEnv = S.emptyEnv


-- TODO: Change type of terms to Term a ()
data Term a b where
  {- Variables -}
  Decl   :: Decl a b   -> Term a b
  Refn   :: Refn a     -> Term a a
  
  {- Modules -}
  Export :: Export a b -> Term a b
  Import :: Import a b -> Term a b
  LetModule :: Term b c -> Term a b -> Term c c -> Term a a
  UseModule :: Term a b -> Term (Join a b) (Join a b) -> Term a a

  {- Magic -}
  Closed  :: ClosedTerm -> Term a a
  RightT  :: Term b c -> Term (Pair a b) (Pair a c)
  LeftT   :: Term a b -> Term (Pair a c) (Pair b c)
  WrapCtx :: Term (Pair () a) (Pair c b) -> Term a b

  {- Core Language -}
  Apply  :: Term a a -> Term a a -> Term a a
  Lambda :: Term a b -> Term b b -> Term a a
  Func   :: Term a b -> Term b c -> Term c c -> Term a b
  Param  :: Term a b -> Term a c -> Term a (Join b c)
  If     :: Term a a -> Term a a -> Term a a -> Term a a
  Seq    :: Term a b -> Term b c -> Term a c
  Num    :: Int -> Term a a

  {- Syntactic Sugar -}
  Let :: Term a b -> Term a a -> Term b b -> Term a a
  Or  :: Term a a -> Term a a -> Term a a


type ClosedTerm = Term () ()

type OpenTerm a b = Scoped a b (Term a b)

data Fresh = forall b. Fresh (forall a. OpenTerm a b)

data Interpreter v s r = Interpreter {
  iDecl :: forall a b. Decl a b -> Env v s a -> (r, Env v s b),
  iRefn :: forall a.   Refn a   -> v -> r,
  iExpt :: forall a b. Export a b -> Env v s a -> (r, Env v s b),
  iImpt :: forall a b. Import a b -> Env v s a -> (r, Env v s b),
  
  iLetModule :: r -> r -> r -> r,
  iUseModule :: r -> r -> r,
  
  iApply  :: r -> r -> r,
  iLambda :: r -> r -> r,
  iFunc   :: r -> r -> r -> r,
  iParam  :: r -> r -> r,
  iIf     :: r -> r -> r -> r,
  iSeq    :: r -> r -> r,
  iNum    :: Int -> r,
  
  iLet    :: r -> r -> r -> r,
  iOr     :: r -> r -> r
}


interpret :: forall v s r. ClosedTerm -> Interpreter v s r -> s -> r
interpret t i s = run t (emptyEnv s) where
  run :: Term a b -> Env v s a -> r
  run t e = fst (interp t e)
  
  interp :: Term a b -> Interp v s r a b
  interp (Decl d) = iDecl i d
  interp (Refn r) = \env -> (iRefn i r (find r env), env)
  interp (Export ex) = iExpt i ex
  interp (Import im) = iImpt i im
  
  interp (Closed t) = \env ->
    let (r, env') = interp t (clearEnv env) in
    (r, env)
  interp (RightT t) = runRightEnv (interp t)
  interp (LeftT t)  = runLeftEnv  (interp t)
  interp (WrapCtx t) = \env ->
    let (r, env') = interp t (liftRightEnv env) in
    (r, lowerRightEnv env')
  
  interp (Apply a b)  = runInterp2 (iApply i)  (interp a) (interp b)
  interp (Lambda x b) = runInterp2 (iLambda i) (interp x) (interp b)
  interp (Param a b)  = joinInterp (iParam i)  (interp a) (interp b)
  interp (If a b c)   = runInterp3 (iIf i)     (interp a) (interp b) (interp c)
  interp (Or a b)     = runInterp2 (iOr i)     (interp a) (interp b)
  interp (Num n) = produce (iNum i n)
  interp (Func f x b) = \env ->
    let (f', envf) = interp f env
        (x', envx) = interp x envf
        (b', _)    = interp b envx in
    (iFunc i f' x' b', envf)
  interp (Seq a b) = \env ->
    let (a', enva) = interp a env
        (b', envb) = interp b enva in
    (iSeq i a' b', envb)
  interp (Let x a b) = \env ->
    let (x', envx) = interp x env
        (a', _)    = interp a env
        (b', _)    = interp b envx in
    (iLet i x' a' b', env)

  interp (LetModule ex mod body) = \env ->
    let (mod', envMod)   = interp mod env
        (ex',  envEx)    = interp ex envMod
        (body', envBody) = interp body envEx in
    (iLetModule i ex' mod' body', env)
  interp (UseModule im body) = \env ->
    let (im', envIm) = interp im env
        (body', _)   = interp body (join env envIm) in
    (iUseModule i im' body', env)


{- Term & Context Construction -}

makeTerm :: Scoped () b (Term a b) -> IO (Term a b)
makeTerm t = return $ fst $ t $ emptyScope

type Ctx a b p q =
  Scope a -> (Term (Pair a p) (Pair b q), Scope b)

term :: OpenTerm a b -> Ctx a b p p
term t a =
  let (t', b) = t a in
  (LeftT t', b)

hole :: Term p q -> Ctx a a p q
hole t a = (RightT t, a)

makeContext:: Ctx () b p q -> IO (Term p q)
makeContext t = return $ WrapCtx $ fst $ t emptyScope


decl :: String -> IO Fresh
decl name = do
  FreshDecl f <- newDecl name
  return $ Fresh $ \s -> let (d, s') = f s in (Decl d, s')

refn :: String -> forall a. OpenTerm a a
refn name s =
  let t = case newRefn name s of
        Right r  -> Refn r
        Left err -> error (show err) in
  (t, s)

tExport :: String -> IO Fresh
tExport name = do
  S.FreshExport f <- newExport name
  return $ Fresh $ \s -> let (ex, s') = f s in (Export ex, s')

tImport :: String -> IO Fresh
tImport name = return $
  case newImport name of
    S.FreshImport f ->
      Fresh $ \s ->
      case f s of
        Right (im, s') -> (Import im, s')
        Left err       -> error (show err)

tLetModule ex mod body s =
  let (mod', sMod) = mod s
      (ex',  sEx)  = ex sMod
      (body', _)   = body sEx in
  (LetModule ex' mod' body', s)

tUseModule im body s =
  let (im', sIm)     = im s
      (body', sBody) = body (join s sIm) in
  (UseModule im' body', sIm)

tParam ab ac sa =
  let (b, sb) = ab sa
      (c, sc) = ac sa in
  (Param b c, join sb sc)

tSeq ab bc sa =
  let (b, sb) = ab sa
      (c, sc) = bc sb in
  (Seq b c, sc)

tApply  = runScoped2 Apply
tLambda = runScoped2 Lambda
tOr     = runScoped2 Or
tIf     = runScoped3 If

tNum n s = (Num n, s)

tLet x a b s =
  let (x', s') = x s
      (a', _)  = a s
      (b', _)  = b s' in
  (Let x' a' b', s)

tFunc f x b s =
  let (f', sf) = f s
      (x', sx) = x sf
      (b', _)  = b sx in
  (Func f' x' b', sf)


subst :: Env (Maybe ClosedTerm) () a -> Term a b -> Term a b
subst env t = fst (sb t env) where
  sb :: Term a b -> Interp (Maybe ClosedTerm) () (Term a b) a b
  
  sb (Decl d) env = (Decl d, bind d Nothing env)
  sb (Refn r) env =
    let t = case find r env of
          Nothing -> Refn r
          Just t  -> Closed t in
    (t, env)
  
  sb (LetModule ex mod body) env =
    let (mod', envMod) = sb mod env
        (ex', envEx)   = sb ex envMod
        (body', _)     = sb body envEx in
    (LetModule ex' mod' body', env)
  sb (UseModule im body) env =
    let (im', envIm) = sb im env
        (body', _)   = sb body (join env envIm) in
    (UseModule im body', env)

  sb (Closed t) env =
    let (t', env') = sb t (emptyEnv ()) in
    (Closed t', env)
  sb (LeftT a) env =
    let (a', env') = runLeftEnv (sb a) env in
    (LeftT a', env')
  sb (RightT b) env =
    let (b', env') = runRightEnv (sb b) env in
    (RightT b', env')
  sb (WrapCtx t) env =
    let (t', env') = sb t (liftRightEnv env) in
    (WrapCtx t', lowerRightEnv env')
  
  sb (Lambda x b) env =
    let (x', envx) = sb x env in
    (Lambda x' (subst envx b), env)
  sb (Param a b) env = joinInterp Param (sb a) (sb b) env
  sb (Let x a b) env =
    let (x', envx) = sb x env
        (a', _)    = sb a env
        (b', _)    = sb b envx in
    (Let x' a' b', env)
  sb (Func f x b) env =
    let (f', envf) = sb f env
        (x', envx) = sb x envf
        (b', _)    = sb b envx in
    (Func f' x' b', envf)
  sb (Seq a b) env =
    let (a', enva) = sb a env
        (b', envb) = sb b enva in
    (Seq a' b', envb)
  sb (Num n)     env = (Num n, env)
  sb (Apply a b) env = (Apply (subst env a) (subst env b), env)
  sb (If a b c)  env = (If    (subst env a) (subst env b) (subst env c), env)
  sb (Or a b)    env = (Or    (subst env a) (subst env b), env)


data ShowState = ShowState Char String -- next var, current module name

interp_show :: Interpreter String ShowState String
interp_show = Interpreter {
  iDecl = \d env ->
     let (v, newEnv) = nextName env
         name = [v] in
     (name, bind d name newEnv),
  iRefn = \_ str -> str,
  iImpt = \im env ->
    let env' = inport im env
        modName = getModName env' in
    (modName, env'),
  iExpt = \ex env ->
    let (v, env') = nextModName env
        envEx = export ex env' in
    ([v], envEx),
  
  iLetModule = \ex mod body ->
    "(let-module (" ++ ex ++ ") " ++ mod ++ " " ++ body ++ ")",
  iUseModule = \im body ->
    "(use-module (" ++ im ++ ") " ++ body ++ ")",
  iLambda = \x b   -> "(lam " ++ x ++ ". " ++ b ++ ")",
  iApply  = \a b   -> "(" ++ a ++ " " ++ b ++ ")",
  iIf     = \a b c -> "(if " ++ a ++ " " ++ b ++ " " ++ c ++ ")",
  iFunc   = \f x b -> "(fun (" ++ f ++ " " ++ x ++ ") " ++ b ++ ")",
  iParam  = \a b   -> a ++ " " ++ b,
  iSeq    = \a b   -> a ++ " " ++ b,
  iNum    = \n     -> show n,
  iLet    = \x a b -> "(let " ++ x ++ " " ++ a ++ " " ++ b ++ ")",
  iOr     = \a b   -> "(or " ++ a ++ " " ++ b ++ ")"
  }
  where
    nextName :: Env String ShowState a -> (Char, Env String ShowState a)
    nextName env =
      let ShowState oldName mod = getState env
          newName = chr (ord oldName + 1)
          newEnv  = setState env (ShowState newName mod) in
      (oldName, newEnv)
  
    nextModName :: Env String ShowState a -> (Char, Env String ShowState a)
    nextModName env =
      let ShowState oldName mod = getState env
          newName = chr (ord oldName + 1)
          newEnv  = setState env (ShowState newName [oldName]) in
      (oldName, newEnv)
    
    getModName :: Env String ShowState a -> String
    getModName env =
      let ShowState _ modName = getState env in
      modName

instance Show ClosedTerm where
  show t = interpret t interp_show (ShowState 'a' "%TOPLEVEL_MODULE")
