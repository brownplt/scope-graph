{-# LANGUAGE GADTs, Rank2Types, ScopedTypeVariables #-}

-- TODO: Change type of terms to Term a ()?

module Term where

import Scope hiding (bind, find, emptyEnv, joinEnv, Env, Decl, Join,
                     FreshImport (FreshImport), FreshExport (FreshExport),
                     getState, setState, inport, export)
import qualified Scope as S


data Term a b where
  {- Variables -}
  Decl   :: Decl a b   -> Term a b
  Refn   :: Refn a     -> Term a a
  
  {- Modules -}
  Export :: Export a b -> Term a b
  Import :: Import a b -> Term a b
  DefModule :: Term b c -> Block a b -> Term a c
  UseModule :: Term a b -> Term (Join a b) (Join a b) -> Term a a

  {- Magic -}
  Closed  :: ClosedTerm -> Term a a
  RightT  :: Term b c -> Term (Pair a b) (Pair a c)
  LeftT   :: Term a b -> Term (Pair a c) (Pair b c)
  WrapCtx :: Term (Pair () a) (Pair c b) -> Term a b

  {- Core Language -}
  Num    :: Int -> Term a a
  Unop   :: Unop -> Term a a -> Term a a
  Binop  :: Binop -> Term a a -> Term a a -> Term a a
  Apply  :: Term a a -> Term a a -> Term a a
  Lambda :: Term a b -> Term b b -> Term a a
  Rec    :: Term a b -> Term b b -> Term a a
  Func   :: Decl a b -> Term b c -> Term c c -> Term a b
  MLink  :: Term a b -> Term a c -> Term a (Join b c)
  Block  :: Block a b -> Term a a
  Define :: Term a b -> Term a a -> Term b b -> Term a b

  {- Syntactic Sugar -}
  Let :: Term a b -> Term a a -> Term b b -> Term a a
  Or  :: Term a a -> Term a a -> Term a a
  If  :: Term a a -> Term a a -> Term a a -> Term a a

data Block a b where
  Seq :: Term a b -> Block b c -> Block a c
  End :: Term a b -> Block a b


data Binop = OpPlus  | OpMult | OpLink
data Unop  = OpFirst | OpRest

instance Show Binop where
  show OpPlus  = "+"
  show OpMult  = "*"
  show OpLink  = "link"

instance Show Unop where
  show OpFirst = "first"
  show OpRest  = "rest"

type ClosedTerm = Term () ()

type OpenTerm a b = Scoped a b (Term a b)

data Fresh = forall b. Fresh (forall a. OpenTerm a b)


{- Interpretation of Terms -}

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

iDefModule :: (r1 -> r2 -> r3)
              -> Interp v s r1 b c
              -> Interp v s r2 a b
              -> Interp v s r3 a c
iDefModule ret ex mod env =
  let (mod',  envMod)  = mod env
      (ex',   envEx)   = ex envMod in
  (ret ex' mod', envEx)

iUseModule :: (r1 -> r2 -> r3)
              -> Interp v s r1 a b
              -> Interp v s r2 (Join a b) (Join a b)
              -> Interp v s r3 a a
iUseModule ret im body env =
  let (im', envIm) = im env
      (body', _)   = body (joinEnv env envIm) in
  (ret im' body', env)

iClosed :: (r1 -> r2)
           -> Interp v s r1 () ()
           -> Interp v s r2 a a
iClosed ret t env =
  let (r, env') = t (clearEnv env) in
  (ret r, env)
  
iRight :: (r1 -> r2)
          -> Interp v s r1 b c
          -> Interp v s r2 (Pair a b) (Pair a c)
iRight ret t env =
  let (t', env') = runRightEnv t env in
  (ret t', env')

iLeft :: (r1 -> r2)
         -> Interp v s r1 a b
         -> Interp v s r2 (Pair a c) (Pair b c)
iLeft ret t env =
  let (t', env') = runLeftEnv t env in
  (ret t', env')

iWrapCtx :: (r1 -> r2)
            -> Interp v s r1 (Pair () a) (Pair c b)
            -> Interp v s r2 a b
iWrapCtx ret t env =
  let (t', env') = t (liftRightEnv env) in
  (ret t', lowerRightEnv env')

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

iLambda :: (r1 -> r2 -> r3)
           -> Interp v s r1 a b
           -> Interp v s r2 b b
           -> Interp v s r3 a a
iLambda ret x b env =
  let (x', envX) = x env
      (b', _)    = b envX in
  (ret x' b', env)

iRec :: (r1 -> r2 -> r3)
        -> Interp v s r1 a b
        -> Interp v s r2 b b
        -> Interp v s r3 a a
iRec ret x b env =
  let (x', envX) = x env
      (b', _)    = b envX in
  (ret x' b', env)

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

iMLink :: (r1 -> r2 -> r3)
          -> Interp v s r1 a b
          -> Interp v s r2 a c
          -> Interp v s r3 a (Join b c)
iMLink ret a b = joinInterp ret a b

iFunc :: (r1 -> r2 -> r3 -> r4)
         -> Interp v s r1 a b
         -> Interp v s r2 b c
         -> Interp v s r3 c c
         -> Interp v s r4 a b
iFunc ret f x b env =  
  let (f', envF) = f env
      (x', envX) = x envF
      (b', _)    = b envX in
  (ret f' x' b', envF)

iSeq :: (r1 -> r2 -> r3)
        -> Interp v s r1 a b
        -> Interp v s r2 b c
        -> Interp v s r3 a c
iSeq ret a b env =
  let (a', envA) = a env
      (b', envB) = b envA in
  (ret a' b', envB)

iEnd :: (r1 -> r2)
        -> Interp v s r1 a b
        -> Interp v s r2 a b
iEnd ret a env =
  let (a', envA) = a env in
  (ret a', envA)

iBlock :: (r1 -> r2)
          -> Interp v s r1 a b
          -> Interp v s r2 a a
iBlock ret a env =
  let (a', _) = a env in
  (ret a', env)

iDefine :: (r1 -> r2 -> r3 -> r4)
           -> Interp v s r1 a b
           -> Interp v s r2 a a
           -> Interp v s r3 b b
           -> Interp v s r4 a b
iDefine ret x a b env =
  let (x', envX) = x env
      (a', _)    = a env
      (b', _)    = b envX in
  (ret x' a' b', envX)

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


{- Term & Context Construction -}

makeTerm :: Scoped () b (Term a b) -> IO (Term a b)
makeTerm t = return $ fst $ t $ emptyScope

data FreshTerm = forall b. FreshTerm (Term () b)

makeFreshTerm :: Scoped () b (Term () b) -> IO FreshTerm
makeFreshTerm t = return $ FreshTerm $ fst $ t emptyScope

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

tDefModule ex mod s = do
  let (mod', sMod) = mod s
      (ex',  sEx)  = ex sMod
  (DefModule ex' mod', sEx)

tUseModule im body s =
  let (im', sIm)     = im s
      (body', sBody) = body (joinScope s sIm) in
  (UseModule im' body', sIm)

tMLink ab ac sa =
  let (b, sb) = ab sa
      (c, sc) = ac sa in
  (MLink b c, joinScope sb sc)

tSeq ab bc sa =
  let (b, sb) = ab sa
      (c, sc) = bc sb in
  (Seq b c, sc)

tEnd a s = (End (fst $ a s), s)

tBlock ab sa =
  let (a, _) = ab sa in
  (Block a, sa)

tLambda ab bb sa =
  let (b, sb) = ab sa
      (c, _)  = bb sb in
  (Lambda b c, sa)

tRec ab bb sa =
  let (b, sb) = ab sa
      (c, _)  = bb sb in
  (Rec b c, sa)

tApply a b s =   (Apply (fst $ a s) (fst $ b s), s)
tOr    a b s =   (Or    (fst $ a s) (fst $ b s), s)
tIf    a b c s = (If    (fst $ a s) (fst $ b s) (fst $ c s), s)

tNum n s = (Num n, s)

tUnop  op a s   = (Unop op (fst $ a s), s)
tBinop op a b s = (Binop op (fst $ a s) (fst $ b s), s)

tDefine x a b s =
  let (x', sX) = x s
      (a', _)  = a s
      (b', _)  = b sX in
  (Let x' a' b', sX)

tLet x a b s =
  let (x', s') = x s
      (a', _)  = a s
      (b', _)  = b s' in
  (Let x' a' b', s)

tFunc f x b s =
  let (Decl f', sf) = f s
      (x', sx) = x sf
      (b', _)  = b sx in
  (Func f' x' b', sf)


{- Exports -}

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

type Decl = S.Decl

type Join = S.Join
