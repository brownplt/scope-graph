{-# LANGUAGE GADTs, Rank2Types, FlexibleInstances, ScopedTypeVariables #-}

-- TODO: Change type of terms to Term a ()?
-- TODO: Remove kind signatures?

module Term where

import Data.Char (ord, chr)

import Scope hiding (bind, find, emptyEnv, Env,
                     FreshImport (FreshImport), FreshExport (FreshExport))
import qualified Scope as S
import Interp

type Env = S.Env

bind :: S.Decl a b -> v -> Env v s a -> Env v s b
bind = S.bind

find :: S.Refn a -> Env v s a -> v
find = S.find

emptyEnv :: s -> Env v s ()
emptyEnv = S.emptyEnv


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
  interp (Or a b)     = runInterp2 (iOr i)     (interp a) (interp b)
  interp (If a b c)   = \env ->
    (iIf i (run a env) (run b env) (run c env), env)
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

tLambda ab bc sa =
  let (b, sb) = ab sa
      (c, _)  = bc sb in
  (Lambda b c, sa)

tApply  = runScoped2 Apply
tOr     = runScoped2 Or
tIf     = runScoped3 If

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


subst :: Env (Maybe ClosedTerm) () a -> Term a b -> Term a b
subst env t = interpret interp_subst t env

interp_subst :: Interpreter (Maybe ClosedTerm) () Term
interp_subst = Interpreter {
  iDecl = \d env -> (Decl d, bind d Nothing env),
  iRefn = \r v ->
    case v of
      Nothing -> Refn r
      Just t  -> Closed t,
  iImpt = \im env -> (Import im, inport im env),
  iExpt = \ex env -> (Export ex, export ex env),
  
  iClosed  = Closed,
  iLeft    = LeftT,
  iRight   = RightT,
  iWrapCtx = WrapCtx,
  
  iLetModule = LetModule,
  iUseModule = UseModule,
  iLambda    = Lambda,
  iApply     = Apply,
  iIf        = If,
  iFunc      = Func,
  iParam     = Param,
  iSeq       = Seq,
  iLet       = Let,
  iOr        = Or,
  iNum       = Num
  }


data ShowState = ShowState Char String -- next var, current module name

newtype ShowResult a b = SR String

instance Show (ShowResult a b) where
  show (SR str) = str

interp_show :: Interpreter String ShowState ShowResult
interp_show = Interpreter {
  iDecl = \d env ->
     let (v, newEnv) = nextName env
         name = [v] in
     (SR name, bind d name newEnv),
  iRefn = \_ str -> SR str,
  iImpt = \im env ->
    let env' = inport im env
        modName = getModName env' in
    (SR modName, env'),
  iExpt = \ex env ->
    let (v, env') = nextModName env
        envEx = export ex env' in
    (SR [v], envEx),
  
  iClosed  = \(SR t) -> (SR t),
  iLeft    = \(SR t) -> (SR t),
  iRight   = \(SR t) -> (SR t),
  iWrapCtx = \(SR t) -> (SR t),
  
  iLetModule = \(SR ex) (SR mod) (SR body) -> SR $
    "(let-module (" ++ ex ++ ") " ++ mod ++ " " ++ body ++ ")",
  iUseModule = \(SR im) (SR body) -> SR $
    "(use-module (" ++ im ++ ") " ++ body ++ ")",
  iLambda = \(SR x) (SR b) -> SR $
            "(lam " ++ x ++ ". " ++ b ++ ")",
  iApply  = \(SR a) (SR b) -> SR $
            "(" ++ a ++ " " ++ b ++ ")",
  iIf     = \(SR a) (SR b) (SR c) -> SR $
            "(if " ++ a ++ " " ++ b ++ " " ++ c ++ ")",
  iFunc   = \(SR f) (SR x) (SR b) -> SR $
            "(fun (" ++ f ++ " " ++ x ++ ") " ++ b ++ ")",
  iParam  = \(SR a) (SR b) -> SR $
            a ++ " " ++ b,
  iSeq    = \(SR a) (SR b) -> SR $
            a ++ " " ++ b,
  iLet    = \(SR x) (SR a) (SR b) -> SR $
            "(let " ++ x ++ " " ++ a ++ " " ++ b ++ ")",
  iOr     = \(SR a) (SR b) -> SR $
            "(or " ++ a ++ " " ++ b ++ ")",
  iNum    = \n -> SR (show n)
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
  show t = show $ interpret interp_show t (emptyEnv init)
    where init = ShowState 'a' "%TOPLEVEL_MODULE"
