{-# LANGUAGE GADTs, FlexibleInstances #-}

module Lang where

import Term

import Data.Char (ord, chr)


subst :: Env (Maybe ClosedTerm) () a -> Term a b -> Term a b
subst env t = interpret interp_subst t env

interp_subst :: Interpretation (Maybe ClosedTerm) () Term
interp_subst = Interpretation {
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
  
  iNum       = Num,
  iBinop     = Binop,
  iLetModule = LetModule,
  iUseModule = UseModule,
  iLambda    = Lambda,
  iApply     = Apply,
  iIf        = If,
  iFunc      = Func,
  iMLink     = MLink,
  iSeq       = Seq,
  iLet       = Let,
  iOr        = Or
  }


data Value where
  VNum :: Int -> Value
  VLink :: Value -> Value -> Value
  VClosure :: Pattern a b -> Term b c -> Env Value () a -> Value

data Pattern a b where
  PDecl :: Decl a b -> Pattern a b
  PLink :: Pattern a b -> Pattern a c -> Pattern a (Join b c)

eval :: Term a b -> Env Value () a -> Value
eval t env = fst (evalTerm t env)

evalTerm :: Term a b -> SimpleInterp Value () Value a b
evalTerm (Refn r) env = (find r env, env)
evalTerm (Num n)  env = (VNum n, env)
evalTerm (Binop op a b) env =
  (applyBinop op (eval a env) (eval b env), env)
evalTerm (Lambda x b) env =
  (VClosure (evalPatt x) b env, env)
evalTerm (Apply f a) env =
  case eval f env of
    VClosure x b env' ->
      let a' = eval a env
          (b', _) = evalTerm b (bindPatt x a' env') in
      (b', env)

applyBinop :: Binop -> Value -> Value -> Value                            
applyBinop OpPlus (VNum a) (VNum b) = VNum (a + b)

{-
  sApply  = \a b   -> "(" ++ a ++ " " ++ b ++ ")",
  sIf     = \a b c -> "(if " ++ a ++ " " ++ b ++ " " ++ c ++ ")",
  sFunc   = \f x b -> "(fun (" ++ f ++ " " ++ x ++ ") " ++ b ++ ")",
  sMLink  = \a b   -> a ++ " " ++ b,
  sSeq    = \a b   -> a ++ " " ++ b,
  sLet    = \x a b -> "(let " ++ x ++ " " ++ a ++ " " ++ b ++ ")",
  sOr     = \a b   -> "(or " ++ a ++ " " ++ b ++ ")"
-}

evalPatt :: Term a b -> Pattern a b
evalPatt (Decl d) = PDecl d
evalPatt (MLink p1 p2) = PLink (evalPatt p1) (evalPatt p2)

bindPatt :: Pattern a b -> Value -> Env Value s a -> Env Value s b
bindPatt (PDecl d) v env = bind d v env
bindPatt (PLink p q) (VLink a b) env =
  joinEnv (bindPatt p a env) (bindPatt q b env)
bindPatt _ _ env = error "Match error"


data ShowState = ShowState Char String -- next var, current module name

interp_show :: SimpleInterpretation String ShowState String
interp_show = SimpleInterpretation {
  sDecl = \d env ->
     let (v, newEnv) = nextName env
         name = [v] in
     (name, bind d name newEnv),
  sRefn = \_ str -> str,
  sImpt = \im env ->
    let env' = inport im env in
    (getModName env', env'),
  sExpt = \ex env ->
    let (v, env') = nextModName env in
    ([v], export ex env'),
  
  sLetModule = \ex mod body ->
    "(let-module (" ++ ex ++ ") " ++ mod ++ " " ++ body ++ ")",
  sUseModule = \im body ->
    "(use-module (" ++ im ++ ") " ++ body ++ ")",
  
  sNum    = \n     -> show n,
  sBinop  = \o a b -> "(" ++ show o ++ " " ++ a ++ " " ++ b ++ ")",
  sLambda = \x b   -> "(lam " ++ x ++ ". " ++ b ++ ")",
  sApply  = \a b   -> "(" ++ a ++ " " ++ b ++ ")",
  sIf     = \a b c -> "(if " ++ a ++ " " ++ b ++ " " ++ c ++ ")",
  sFunc   = \f x b -> "(fun (" ++ f ++ " " ++ x ++ ") " ++ b ++ ")",
  sMLink  = \a b   -> a ++ " " ++ b,
  sSeq    = \a b   -> a ++ " " ++ b,
  sLet    = \x a b -> "(let " ++ x ++ " " ++ a ++ " " ++ b ++ ")",
  sOr     = \a b   -> "(or " ++ a ++ " " ++ b ++ ")"
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
  show t = show $ simpleInterpret interp_show t (emptyEnv init)
    where init = ShowState 'a' "%TOPLEVEL_MODULE"
