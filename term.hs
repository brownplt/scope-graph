{-# LANGUAGE GADTs, Rank2Types, FlexibleInstances #-}

module Term where

import Data.Char (ord, chr)

import Scope hiding (bind, find, emptyEnv,
                     FreshImport (FreshImport), FreshExport (FreshExport))
import qualified Scope as S

bind :: EnvState s => S.Decl a b -> v -> Env v s a -> Env v s b
bind = S.bind

find :: S.Refn a -> Env v s a -> v
find = S.find

emptyEnv :: EnvState s => Env v s ()
emptyEnv = S.emptyEnv


data Term a b where
  {- Variables -}
  Decl   :: Decl a b   -> Term a b
  Refn   :: Refn a     -> Term a a
  
  {- Modules -}
  LetModule :: Export b c -> Term a b -> Term c c -> Term a a
  UseModule :: Import a b -> Term (Join a b) (Join a b) -> Term a a

  {- Magic -}
  Closed  :: Term () () -> Term a a
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


{- Term & Context Construction -}

type OpenTerm a b = Scoped a b (Term a b)

data Fresh = forall b. Fresh (forall a. OpenTerm a b)

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

data FreshExport =
  forall b. FreshExport (forall a. Scoped a b (Export a b))

expt :: String -> IO FreshExport
expt name = do
  S.FreshExport ex <- newExport name
  return $ FreshExport ex

data FreshImport =
  forall b. FreshImport (forall a. (String, Scoped a b (Import a b)))

impt:: String -> IO FreshImport
impt name = return $
  case newImport name of
    S.FreshImport f ->
      FreshImport (name, \s ->
      case f s of
        Right im -> im
        Left err -> error (show err))

tLetModule ex mod body s =
  let (mod', sMod) = mod s
      (ex',  sEx)  = ex sMod
      (body', _)   = body sEx in
  (LetModule ex' mod' body', s)

tUseModule (name, im) body s =
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

--tLet x a b =
--  runScoped3 (\a x b -> Let x a b) a x b

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


instance EnvState () where
  emptyState = ()
  joinState () () = ()

subst :: Env (Maybe (Term () ())) () a -> Term a b -> Term a b
subst env t = fst (sb env t) where
  sb :: Env (Maybe (Term () ())) () a -> Term a b
        -> (Term a b, Env (Maybe (Term () ())) () b)
  
  sb env (Decl d) = (Decl d, bind d Nothing env)
  sb env (Refn r) =
    let t = case find r env of
          Nothing -> Refn r
          Just t  -> Closed t in
    (t, env)
  
  sb env (LetModule ex mod body) =
    let (mod', envMod) = sb env mod
        envEx          = export ex () envMod
        (body', _)     = sb envEx body in
    (LetModule ex mod' body', env)
  sb env (UseModule im body) =
    let envIm = inport im env
        (body', _)   = sb (join env envIm) body in
    (UseModule im body', env)

  sb env (Closed t) =
    let (t', env') = sb emptyEnv t in
    (Closed t', env)
  sb env (LeftT a) =
    let (envL, envR) = unpairEnv env
        (a', envL') = sb envL a in
    (LeftT a', pairEnv envL' envR ())
  sb env (RightT b) =
    let (envL, envR) = unpairEnv env
        (b', envR') = sb envR b in
    (RightT b', pairEnv envL envR' ())
  sb env (WrapCtx t) =
    let (t', env') = sb (pairEnv emptyEnv env ()) t in
    (WrapCtx t', snd $ unpairEnv env')
  
  sb env (Lambda x b) =
    let (x', envx) = sb env x in
    (Lambda x' (subst envx b), env)
  sb env (Param a b) =
    let (a', enva) = sb env a
        (b', envb) = sb env b in
    (Param a' b', join enva envb)
  sb env (Let x a b) =
    let (x', envx) = sb env x
        (a', _)    = sb env a
        (b', _)    = sb envx b in
    (Let x' a' b', env)
  sb env (Func f x b) =
    let (f', envf) = sb env f
        (x', envx) = sb envf x
        (b', _)    = sb envx b in
    (Func f' x' b', envf)
  sb env (Seq a b) =
    let (a', enva) = sb env a
        (b', envb) = sb enva b in
    (Seq a' b', envb)
  sb env (Num n)     = (Num n, env)
  sb env (Apply a b) = (Apply (subst env a) (subst env b), env)
  sb env (If a b c)  = (If    (subst env a) (subst env b) (subst env c), env)
  sb env (Or a b)    = (Or    (subst env a) (subst env b), env)


data ShowState = ShowState Char String -- next var, current module name

instance EnvState ShowState where
  emptyState = ShowState 'a' "%TOPLEVEL_MODULE"
  joinState a b = a -- ???


instance Show (Term () ()) where
  show t = let (str, _) = sh t emptyEnv
           in str where
    sh :: Term a b -> Env String ShowState a -> (String, Env String ShowState b)
    -- a b c t: subterms
    -- env: mapping from variables to their names
    -- v: the next variable name to use (don't use more than 26).

    sh (Decl d) env =
      let (v, newEnv) = nextName env
          name = [v] in
      (name, bind d name newEnv)
    sh (Refn r) env = (find r env, env)
    
    sh (LetModule ex mod body) env =
      let (v, newEnv)      = nextModName env
          (strMod, envMod) = sh mod newEnv
          envEx            = export ex (getState envMod) envMod -- ???
          (strBody, _)     = sh body envEx in
      ("(let-module (" ++ [v] ++ ") " ++ strMod ++ " " ++ strBody ++ ")",
       env)
    sh (UseModule im body) env =
      let ShowState _ modName = getState env
          envIm = inport im env
          (strBody, _) = sh body (join env envIm) in
      ("(use-module (" ++ modName ++ ") " ++ strBody ++ ")", env)

    sh (LeftT t) env =
      let st = getState env
          (envL, envR) = unpairEnv env
          (str, envL') = sh t envL in
      (str, pairEnv envL' envR st)
    sh (RightT t) env =
      let st = getState env
          (envL, envR) = unpairEnv env
          (str, envR') = sh t envR in
      (str, pairEnv envL envR' st)
    sh (Closed t) env =
      let st = getState env
          (str, _) = sh t (setState emptyEnv st) in
      (str, env)
    sh (WrapCtx t) env =
      let st = getState env
          (str, env') = sh t (pairEnv emptyEnv env st) in
      (str, snd (unpairEnv env'))
    
    sh (Num n) env = (show n, env)
    sh (Param a b) env =
      let (strA, envA) = sh a env
          stA = getState envA
          (strB, envB) = sh b (setState env stA) in
      (strA ++ " " ++ strB, join envA envB)
    sh (Apply a b) env =
      let (strA, _) = sh a env
          (strB, _) = sh b env in
      ("(" ++ strA ++ " " ++ strB ++ ")", env)
    sh (Lambda x b) env =
      let (strX, envX) = sh x env
          (strB, _)    = sh b envX in
      ("(lam " ++ strX ++ ". " ++ strB ++ ")", env)
    sh (If a b c) env =
      let (strA, _) = sh a env
          (strB, _) = sh b env
          (strC, _) = sh c env in
      ("if " ++ strA ++ " " ++ strB ++ " " ++ strC ++ ")", env)
    sh (Let x a b) env =
      let (strX, envX) = sh x env
          (strA, _)    = sh a env
          (strB, _)    = sh b envX in
      ("(let " ++ strX ++ " " ++ strA ++ " " ++ strB ++ ")", env)
    sh (Or a b) env =
      let (strA, _) = sh a env
          (strB, _) = sh b env in
      ("(or " ++ strA ++ " " ++ strB ++ ")", env)
    sh (Func f x b) env =
      let (strF, envF) = sh f env
          (strX, envX) = sh x envF
          (strB, _)    = sh b envX in
      ("(fun (" ++ strF ++ " " ++ strX ++ ") " ++ strB ++ ")", envF)
    sh (Seq a b) env =
      let (strA, envA) = sh a env
          (strB, envB) = sh b envA in
      (strA ++ " " ++ strB, envB)

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

-- instance Show (Term a b) where show t = "term"

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
