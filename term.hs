{-# LANGUAGE GADTs, Rank2Types, ScopedTypeVariables #-}

-- TODO: Change type of terms to Term a ()?
-- TODO: Remove kind signatures?

module Term where

import Scope hiding (bind, find, emptyEnv, Env,
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


{- Interpretation of Terms -}

type Interp v s r a b = Env v s a -> (r a b, Env v s b)

joinInterp :: (r a b -> r a c -> r a (Join b c))
        -> Interp v s r a b
        -> Interp v s r a c
        -> Interp v s r a (Join b c)
joinInterp f i1 i2 env =
  let (r1, env1) = i1 env
      (r2, env2) = i2 (setState env (getState env1)) in
  (f r1 r2, join env1 env2)


data Interpreter v s r = Interpreter {
  iDecl :: forall a b. Decl a b -> Env v s a -> (r a b, Env v s b),
  iRefn :: forall a.   Refn a   -> v -> r a a,
  iExpt :: forall a b. Export a b -> Env v s a -> (r a b, Env v s b),
  iImpt :: forall a b. Import a b -> Env v s a -> (r a b, Env v s b),
  
  iLetModule :: forall a b c. r b c -> r a b -> r c c -> r a a,
  iUseModule :: forall a b.   r a b -> r (Join a b) (Join a b) -> r a a,
  
  iClosed :: forall a.     r () () -> r a a,
  iRight  :: forall a b c. r b c -> r (Pair a b) (Pair a c),
  iLeft   :: forall a b c. r a b -> r (Pair a c) (Pair b c),
  iWrapCtx :: forall a b c. r (Pair () a) (Pair c b) -> r a b,
  
  iApply  :: forall a.     r a a -> r a a -> r a a,
  iLambda :: forall a b.   r a b -> r b b -> r a a,
  iFunc   :: forall a b c. r a b -> r b c -> r c c -> r a b,
  iParam  :: forall a b c. r a b -> r a c -> r a (Join b c),
  iIf     :: forall a.     r a a -> r a a -> r a a -> r a a,
  iSeq    :: forall a b c. r a b -> r b c -> r a c,
  iNum    :: forall a.   Int -> r a a,

  iLet    :: forall a b. r a b -> r a a -> r b b -> r a a,
  iOr     :: forall a.   r a a -> r a a -> r a a
}


interpret :: forall v s r p q.
             Interpreter v s r -> Term p q -> Env v s p -> r p q
interpret i t env = run t env where
  run :: Term a b -> Env v s a -> r a b
  run t e = fst (interp t e)
  
  interp :: Term a b -> Interp v s r a b
  interp (Decl d) = iDecl i d
  interp (Refn r) = \env -> (iRefn i r (find r env), env)
  interp (Export ex) = iExpt i ex
  interp (Import im) = iImpt i im
  
  interp (Closed t) = \env ->
    let (r, env') = interp t (clearEnv env) in
    (iClosed i r, env)
  interp (RightT t) = \env ->
    let (r, env') = runRightEnv (interp t) env in
    (iRight i r, env')
  interp (LeftT t) = \env ->
    let (r, env') = runLeftEnv (interp t) env in
    (iLeft i r, env')
  interp (WrapCtx t) = \env ->
    let (r, env') = interp t (liftRightEnv env) in
    (iWrapCtx i r, lowerRightEnv env')
  
  interp (Apply a b) = \env ->
    (iApply i (run a env) (run b env), env)
  interp (Lambda x b) = \env ->
    let (x', envx) = interp x env
        (b', _)    = interp b envx in
    (iLambda i x' b', env)
  interp (Param a b)  = joinInterp (iParam i)  (interp a) (interp b)
  interp (Or a b) = \env ->
    (iOr i (run a env) (run b env), env)
  interp (If a b c)   = \env ->
    (iIf i (run a env) (run b env) (run c env), env)
  interp (Num n) = \env -> (iNum i n, env)
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


-- Most interpretations' return values don't neeed to be
-- parameterized over scope variables.

data SimpleInterpreter v s r = SimpleInterpreter {
  sDecl :: forall a b. Decl a b -> Env v s a -> (r, Env v s b),
  sRefn :: forall a.   Refn a   -> v -> r,
  sExpt :: forall a b. Export a b -> Env v s a -> (r, Env v s b),
  sImpt :: forall a b. Import a b -> Env v s a -> (r, Env v s b),
  
  sLetModule :: r -> r -> r -> r,
  sUseModule :: r -> r -> r,
  
  sApply  :: r -> r -> r,
  sLambda :: r -> r -> r,
  sFunc   :: r -> r -> r -> r,
  sParam  :: r -> r -> r,
  sIf     :: r -> r -> r -> r,
  sSeq    :: r -> r -> r,
  sNum    :: Int -> r,
  
  sLet    :: r -> r -> r -> r,
  sOr     :: r -> r -> r
}


newtype SimpleResult r a b = SimpleResult r

liftSimpleInterpreter :: SimpleInterpreter v s r
                         -> Interpreter v s (SimpleResult r)
liftSimpleInterpreter i = Interpreter {
  iDecl = \d env -> let (r, env') = sDecl i d env in
   (SimpleResult r, env'),
  iRefn = \r v -> SimpleResult (sRefn i r v),
  iExpt = \ex env -> let (r, env') = sExpt i ex env in
   (SimpleResult r, env'),
  iImpt = \im env -> let (r, env') = sImpt i im env in
   (SimpleResult r, env'),
  
  iClosed  = lift0,
  iLeft    = lift0,
  iRight   = lift0,
  iWrapCtx = lift0,
  
  iLetModule = lift3 (sLetModule i),
  iUseModule = lift2 (sUseModule i),
  
  iApply     = lift2 (sApply i),
  iLambda    = lift2 (sLambda i),
  iFunc      = lift3 (sFunc i),
  iParam     = lift2 (sParam i),
  iIf        = lift3 (sIf i),
  iSeq       = lift2 (sSeq i),
  iNum       = \n -> SimpleResult (sNum i n),
  
  iLet       = lift3 (sLet i),
  iOr        = lift2 (sOr i)
  }
  where
    lift0 (SimpleResult a) = SimpleResult a
    lift1 f (SimpleResult a) = SimpleResult (f a)
    lift2 f (SimpleResult a) (SimpleResult b) = SimpleResult (f a b)
    lift3 f (SimpleResult a) (SimpleResult b) (SimpleResult c) =
      SimpleResult (f a b c)

simpleInterpret :: forall v s r p q.
                   SimpleInterpreter v s r
                   -> Term p q
                   -> Env v s p
                   -> r
simpleInterpret i t e =
  let SimpleResult r = interpret (liftSimpleInterpreter i) t e in
  r


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

tLambda ab bc sa =
  let (b, sb) = ab sa
      (c, _)  = bc sb in
  (Lambda b c, sa)

tApply a b s =   (Apply (fst $ a s) (fst $ b s), s)
tOr    a b s =   (Or    (fst $ a s) (fst $ b s), s)
tIf    a b c s = (If    (fst $ a s) (fst $ b s) (fst $ c s), s)

tNum n s = (Num n, s)

tLet x a b s =
  let (x', s') = x s
      (a', _)  = a s
      (b', _)  = b s' in
  (Let x' a' b', emptyScope)

tFunc f x b s =
  let (f', sf) = f s
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

emptyEnv :: s -> Env v s ()
emptyEnv = S.emptyEnv
