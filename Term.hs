{-# LANGUAGE GADTs, Rank2Types, ScopedTypeVariables #-}

-- TODO: Change type of terms to Term a ()?

module Term where

import Scope hiding (bind, find, emptyEnv, joinEnv, Env, Join,
                     FreshImport (FreshImport), FreshDecl (FreshDecl),
                     Decl, Import, Export,
                     getState, setState, inport, export)
import qualified Scope as S

data Expr a where
  Refn   :: Refn a -> Expr a
  Num    :: Int -> Expr a
  Unop   :: Unop  -> Expr a -> Expr a
  Binop  :: Binop -> Expr a -> Expr a -> Expr a
  Apply  :: Expr a   -> Expr a -> Expr a
  Lambda :: Patt a b -> Expr b -> Expr a
  IfCase :: Expr a   -> Patt a b -> Expr b -> Expr a -> Expr a
  Stmt   :: Stmt a b -> Expr a
  {- Sugar -}
  Let :: Patt a b -> Expr a -> Expr b -> Expr a
  Or  :: Expr a -> Expr a -> Expr a
  If  :: Expr a -> Expr a -> Expr a -> Expr a
  Match :: Expr a -> Cases a -> Expr a
  {- Magic -}
  ERight :: Expr b -> Expr (Pair a b)
  ELeft  :: Expr a -> Expr (Pair a b)
  ECtx   :: Expr (Pair () a) -> Expr a

data Cases a where
  Case :: Patt a b -> Expr b -> Cases a -> Cases a
  Else :: Expr a -> Cases a

data Patt a b where
  PDecl :: Decl a b -> Patt a b
  PNum  :: Int -> Patt a a
  PLink :: Patt a b -> Patt a c -> Patt a (Join b c)
  {- Magic -}
  PLeft  :: Patt a b -> Patt (Pair a p) (Pair b p)
  PRight :: Patt p q -> Patt (Pair a p) (Pair a q)

data Stmt a b where
  End    :: Expr a -> Stmt a a
  Define :: Patt a b -> Expr a -> Stmt b c -> Stmt a c
  Module :: Export b c -> Stmt a b -> Stmt c d -> Stmt a d
  UseMod :: Import a b -> Stmt (Join a b) c -> Stmt a (Join a c)
  {- Sugar -}
  Func   :: Decl a b -> Patt (Join b c) d -> Expr d -> Stmt b c -> Stmt a (Join b c)


data Binop = OpPlus  | OpMult | OpLink | OpEq
data Unop  = OpFirst | OpRest

instance Show Binop where
  show OpPlus  = "+"
  show OpMult  = "*"
  show OpLink  = "link"
  show OpEq    = "=="

instance Show Unop where
  show OpFirst = "first"
  show OpRest  = "rest"

instance Show (Patt a b) where
  show (PDecl _) = "_"
  show (PNum n)  = show n
  show (PLink a b) = "(link " ++ show a ++ " " ++ show b ++ ")"
  show (PLeft a) = show a
  show (PRight a) = show a

data FreshPatt   = forall b. FreshPatt   (forall a. Scoped a b (Patt a b))
data FreshImport = forall b. FreshImport (forall a. Scoped a b (Import a b))
data FreshDecl   = forall b. FreshDecl   (forall a. Scoped a b (Decl a b))

type OpenPatt a b = Scoped a b (Patt a b)

type OpenExpr a = Scoped a a (Expr a)
type ClosedExpr = Expr ()

type OpenStmt a b = Scoped a b (Stmt a b)
type ClosedStmt = Stmt () ()


{- Expr & Context Construction -}

makeExpr :: Scoped () () ClosedExpr -> ClosedExpr
makeExpr t = fst $ t $ emptyScope

data FreshStmt = forall a. FreshStmt (Stmt () a)

makeStmt :: Scoped () () ClosedStmt -> ClosedStmt
makeStmt t = fst $ t $ emptyScope

makeFreshStmt :: Scoped () a (Stmt () a) -> FreshStmt
makeFreshStmt t = FreshStmt $ fst $ t emptyScope

type Ctx a b p =
  Scope a -> (Expr (Pair a p), Scope b)

expr :: OpenExpr a -> Ctx a a p
expr t a =
  let (t', b) = t a in
  (ELeft t', b)

type PattCtx a b p q =
  Scope a -> (Patt (Pair a p) (Pair b q), Scope b)

patt :: OpenPatt a b -> PattCtx a b p p
patt p a =
  let (p', b) = p a in
  (PLeft p', b)

pattHole :: Patt p q -> PattCtx a a p q
pattHole p a = (PRight p, a)

hole :: Expr p -> Ctx a a p
hole t a = (ERight t, a)

makeContext:: Ctx () a p -> Expr p
makeContext t = ECtx $ fst $ t emptyScope


{- Building Terms -}

refn :: String -> forall a. OpenExpr a
refn name s =
  let t = case newRefn name s of
        Right r  -> Refn r
        Left err -> error (show err) in
  (t, s)

decl :: String -> IO FreshDecl
decl name = do
  S.FreshDecl d <- newDecl name
  return (FreshDecl d)

expt :: String -> IO FreshExport
expt = newExport

impt :: String -> IO FreshImport
impt name = return $
  case newImport name of
    S.FreshImport f ->
      FreshImport $ \s ->
      case f s of
        Right ok -> ok
        Left err -> error (show err)

pDecl :: String -> IO FreshPatt
pDecl name = do
  S.FreshDecl f <- newDecl name
  return $ FreshPatt $ \s ->
    let (d, s') = f s in
    (PDecl d, s')

tPNum n s = (PNum n, s)

tPLink a b s =
  let (a', sa) = a s
      (b', sb) = b s in
  (PLink a' b', joinScope sa sb)

tNum n s = (Num n, s)

tUnop  op a s   = (Unop  op (fst $ a s)            , s)
tBinop op a b s = (Binop op (fst $ a s) (fst $ b s), s)
tApply a b s    = (Apply (fst $ a s) (fst $ b s)   , s)
tStmt a s       = (Stmt  (fst $ a s)               , s)
tOr    a b s    = (Or (fst $ a s) (fst $ b s), s)
tIf    a b c s  = (If (fst $ a s) (fst $ b s) (fst $ c s), s)
tMatch a b s    = (Match (fst $ a s) (fst $ b s), s)
tElse a s       = (Else (fst $ a s), s)

tLambda a b s =
  let (a', sA) = a s
      (b', _)  = b sA in
  (Lambda a' b', sA)

tCase x a b s =
  let (x', sX) = x s
      (a', _)  = a sX
      (b', _)  = b s in
  (Case x' a' b', sX)

tIfCase a x b c s =
  let (a', _)  = a s
      (x', sX) = x s
      (b', _)  = b sX
      (c', _)  = c s in
  (IfCase a' x' b' c', s)

tLet x a b s =
  let (x', s') = x s
      (a', _)  = a s
      (b', _)  = b s' in
  (Let x' a' b', s)

tEnd a s =
  let (a', _) = a s in
  (End a', s)

tDefine x a b s =
  let (x', sX) = x s
      (a', _)  = a s
      (b', _)  = b sX in
  (Let x' a' b', sX)

tFunc f x a b s =
  let (f', sF) = f s
      (b', sB) = b sF
      (x', sX) = x (joinScope sF sB)
      (a', _)  = a sX in
  (Func f' x' a' b', (joinScope sF sB))

tModule ex mod b s =
  let (mod', sMod) = mod s
      (ex',  sEx)  = ex sMod
      (b',   sB)   = b sEx in
  (Module ex' mod' b', sB)

tUseMod im b s =
  let (im', sIm) = im s
      (b',  sB)  = b (joinScope s sIm) in
  (UseMod im' b', (joinScope s sB))


{- Interpretation of Exprs -}

type Interp v s r a b = Env v s a -> (r, Env v s b)

joinInterp :: (r1 -> r2 -> r3)
              -> Interp v s r1 a b
              -> Interp v s r2 a c
              -> Interp v s r3 a (Join b c)
joinInterp f i1 i2 env =
  let (r1, env1) = i1 env
      (r2, env2) = i2 (setState env (getState env1)) in
  (f r1 r2, joinEnv env1 env2)


iRefn :: (v -> r)
         -> Refn a
         -> Interp v s r a a
iRefn ret r env = (ret (find r env), env)

iNum :: (Int -> r)
        -> Int
        -> Interp v s r a a
iNum ret n env = (ret n, env)

iUnop :: (op -> r1 -> r2)
         -> op
         -> Interp v s r1 a a
         -> Interp v s r2 a a
iUnop ret op arg env =
  (ret op (fst $ arg env), env)

iBinop :: (op -> r1 -> r2 -> r3)
          -> op
          -> Interp v s r1 a a
          -> Interp v s r2 a a
          -> Interp v s r3 a a
iBinop ret op arg1 arg2 env =
  (ret op (fst $ arg1 env) (fst $ arg2 env), env)

iApply :: (r1 -> r2 -> r3)
          -> Interp v s r1 a a
          -> Interp v s r2 a a
          -> Interp v s r3 a a
iApply ret fun args env =
  (ret (fst $ fun env) (fst $ args env), env)

iMatch :: (r1 -> r2 -> r3)
          -> Interp v s r1 a a
          -> Interp v s r2 a a
          -> Interp v s r3 a a
iMatch ret a b env =
  (ret (fst $ a env) (fst $ b env), env)
  
iCase :: (r1 -> r2 -> r3 -> r4)
         -> Interp v s r1 a b
         -> Interp v s r2 b b
         -> Interp v s r3 a a
         -> Interp v s r4 a a
iCase ret x a b env =
  let (x', envX) = x env
      (a', _)    = a envX
      (b', _)    = b env in
  (ret x' a' b', env)

iElse :: (r1 -> r2)
         -> Interp v s r1 a a
         -> Interp v s r2 a a
iElse ret a env =
  (ret (fst $ a env), env)

iIfCase :: (r1 -> r2 -> r3 -> r4 -> r5)
           -> Interp v s r1 a a
           -> Interp v s r2 a b
           -> Interp v s r3 b b
           -> Interp v s r4 a a
           -> Interp v s r5 a a
iIfCase ret a x b c env =
  let (a', _)    = a env
      (x', envX) = x env
      (b', _)    = b envX
      (c', _)    = c env in
  (ret a' x' b' c', env)

iLambda :: (r1 -> r2 -> r3)
           -> Interp v s r1 a b
           -> Interp v s r2 b b
           -> Interp v s r3 a a
iLambda ret x b env =
  let (x', envX) = x env
      (b', _)    = b envX in
  (ret x' b', env)

iStmt :: (r1 -> r2)
          -> Interp v s r1 a b
          -> Interp v s r2 a a
iStmt ret a env =
  let (a', _) = a env in
  (ret a', env)

iEClosed :: (r1 -> r2)
           -> Interp v s r1 () ()
           -> Interp v s r2 a a
iEClosed ret t env =
  let (r, env') = t (clearEnv env) in
  (ret r, env)

iERight :: (r1 -> r2)
          -> Interp v s r1 p q
          -> Interp v s r2 (Pair a p) (Pair a q)
iERight ret t env =
  let (t', env') = runRightEnv t env in
  (ret t', env')

iELeft :: (r1 -> r2)
         -> Interp v s r1 a b
         -> Interp v s r2 (Pair a p) (Pair b p)
iELeft ret t env =
  let (t', env') = runLeftEnv t env in
  (ret t', env')

iECtx :: (r1 -> r2)
        -> Interp v s r1 (Pair () a) (Pair () a)
        -> Interp v s r2 a a
iECtx ret t env =
  let (t', env') = t (liftRightEnv env) in
  (ret t', lowerRightEnv env')

iPNum :: r -> Interp v s r a a
iPNum ret env = (ret, env)

iPDecl :: (r1 -> r2)
          -> Interp v s r1 a b
          -> Interp v s r2 a b
iPDecl ret d env =
  let (d', env') = d env in
  (ret d', env')

iPLink :: (r1 -> r2 -> r3)
          -> Interp v s r1 a b
          -> Interp v s r2 a c
          -> Interp v s r3 a (Join b c)
iPLink ret a b = joinInterp ret a b

iPRight :: (r1 -> r2)
          -> Interp v s r1 p q
          -> Interp v s r2 (Pair a p) (Pair a q)
iPRight ret t env =
  let (t', env') = runRightEnv t env in
  (ret t', env')

iPLeft :: (r1 -> r2)
         -> Interp v s r1 a b
         -> Interp v s r2 (Pair a p) (Pair b p)
iPLeft ret t env =
  let (t', env') = runLeftEnv t env in
  (ret t', env')

iLet :: (r1 -> r2 -> r3 -> r4)
        -> Interp v s r1 a b
        -> Interp v s r2 a a
        -> Interp v s r3 b b
        -> Interp v s r4 a a
iLet ret x a b env =
  let (x', envX) = x env
      (a', _)    = a env
      (b', _)    = b envX in
  (ret x' a' b', env)

iOr :: (r1 -> r2 -> r3)
       -> Interp v s r1 a a
       -> Interp v s r2 a a
       -> Interp v s r3 a a
iOr ret a b env =
  (ret (fst $ a env) (fst $ b env), env)

iIf :: (r1 -> r2 -> r3 -> r4)
       -> Interp v s r1 a a
       -> Interp v s r2 a a
       -> Interp v s r3 a a
       -> Interp v s r4 a a
iIf ret a b c env =
  (ret (fst $ a env) (fst $ b env) (fst $ c env), env)

iEnd :: (r1 -> r2)
        -> Interp v s r1 a a
        -> Interp v s r2 a a
iEnd ret a env =
  (ret (fst $ a env), env)

iDefine :: (r1 -> r2 -> r3 -> r4)
           -> Interp v s r1 a b
           -> Interp v s r2 a a
           -> Interp v s r3 b c
           -> Interp v s r4 a c
iDefine ret x a b env =
  let (x', envX) = x env
      (a', _)    = a env
      (b', envB) = b envX in
  (ret x' a' b', envB)

iFunc :: (r1 -> r2 -> r3 -> r4 -> r5)
         -> Interp v s r1 a b
         -> Interp v s r2 (Join b c) d
         -> Interp v s r3 d d
         -> Interp v s r4 b c
         -> Interp v s r5 a (Join b c)
iFunc ret f x a b env =
  let (f', envF) = f env
      (b', envB) = b envF
      (x', envX) = x (joinEnv envF envB)
      (a', _)    = a envX in
  (ret f' x' a' b', joinEnv envF envB)
  
iModule :: (r1 -> r2 -> r3 -> r4)
           -> Interp v s r1 b c
           -> Interp v s r2 a b
           -> Interp v s r3 c d
           -> Interp v s r4 a d
iModule ret ex mod b env =
  let (mod', envMod) = mod env
      (ex',  envEx)  = ex envMod
      (b',   envB)   = b envEx in
  (ret ex' mod' b', envB)

iUseMod :: (r1 -> r2 -> r3)
           -> Interp v s r1 a b
           -> Interp v s r2 (Join a b) c
           -> Interp v s r3 a (Join a c)
iUseMod ret im b env =
  let (im', envIm) = im env
      (b', envB)   = b (joinEnv env envIm) in
  (ret im' b', (joinEnv env envB))


{- Provided Names -}

type Env = S.Env

bind :: S.Decl a b -> v -> Env v s a -> Env v s b
bind = S.bind

find :: S.Refn a -> Env v s a -> v
find = S.find

inport = S.inport
export = S.export
getState = S.getState
setState = S.setState

joinEnv :: Env v s a -> Env v s b -> Env v s (Join a b)
joinEnv = S.joinEnv

emptyEnv :: s -> Env v s ()
emptyEnv = S.emptyEnv

type Join = S.Join

type Decl = S.Decl
type Import = S.Import
type Export = S.Export
