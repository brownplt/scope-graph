{-# LANGUAGE GADTs, FlexibleInstances #-}

module Lang where

import Term

import Data.Char (ord, chr)
import Text.Printf (printf)


subst :: Env (Maybe ClosedTerm) () a -> Term a b -> Term a b
subst env t = fst $ sub t env
  where
    sub :: Term a b -> Interp (Maybe ClosedTerm) () (Term a b) a b
    sub (Decl d) = \env -> (Decl d, bind d Nothing env)
    sub (Refn r) = iRefn subRefn r where
      subRefn Nothing  = Refn r
      subRefn (Just t) = Closed t
    sub (Import im) = \env -> (Import im, inport im env)
    sub (Export ex) = \env -> (Export ex, export ex env)
    
    sub (Closed  t) = iClosed  Closed  (sub t)
    sub (LeftT   t) = iLeft    LeftT   (sub t)
    sub (RightT  t) = iRight   RightT  (sub t)
    sub (WrapCtx t) = iWrapCtx WrapCtx (sub t)

    sub (Num n)           = iNum       Num       n
    sub (Unop op a)       = iUnop      Unop      op      (sub a)
    sub (Binop op a b)    = iBinop     Binop     op      (sub a) (sub b)
    sub (LetModule a b c) = iLetModule LetModule (sub a) (sub b) (sub c)
    sub (UseModule a b)   = iUseModule UseModule (sub a) (sub b)
    sub (Lambda x b)      = iLambda    Lambda    (sub x) (sub b)
    sub (Apply a b)       = iApply     Apply     (sub a) (sub b)
    sub (If a b c)        = iIf        If        (sub a) (sub b) (sub c)
    sub (Func a b c)      = iFunc      Func      (sub a) (sub b) (sub c)
    sub (MLink a b)       = iMLink     MLink     (sub a) (sub b)
    sub (Let a b c)       = iLet       Let       (sub a) (sub b) (sub c)
    sub (Seq a b)         = iSeq       Seq       (sub a) (sub b)
    sub (Or a b)          = iOr        Or        (sub a) (sub b)
    


data ShowState = ShowState Char String -- next var, current module name

instance Show ClosedTerm where
  show t = fst $ sh t (emptyEnv (ShowState 'a' "%TOPLEVEL_MODULE")) where
    
    sh :: Term a b -> Interp String ShowState String a b
    sh (Decl d) = \env ->
      let (v, newEnv) = nextName env
          name = [v] in
      (name, bind d name newEnv)
    sh (Refn r) = iRefn id r
    sh (Import im) = \env ->
      let env' = inport im env in
      (getModName env', env')
    sh (Export ex) = \env ->
      let (v, env') = nextModName env in
      ([v], export ex env')
    
    sh (Closed  t) = iClosed  id (sh t)
    sh (LeftT   t) = iLeft    id (sh t)
    sh (RightT  t) = iRight   id (sh t)
    sh (WrapCtx t) = iWrapCtx id (sh t)
    
    sh (LetModule ex mod body) = iLetModule
      (printf "(let-module (%s = %s) %s)") (sh ex) (sh mod) (sh body)
    sh (UseModule im body) = iUseModule
      (printf "(use-module (%s) %s)") (sh im) (sh body)
    sh (Num n)      = iNum    show n
    sh (Unop op a)  = iUnop   (printf "(%s %s)") (show op) (sh a)
    sh (Binop op a b)=iBinop  (printf "(%s %s %s)") (show op) (sh a) (sh b)
    sh (Lambda x b) = iLambda (printf "(lam %s %s)") (sh x) (sh b)
    sh (Apply f a)  = iApply  (printf "(%s %s)") (sh f) (sh a)
    sh (If a b c)   = iIf     (printf "(if %s %s %s)") (sh a) (sh b) (sh c)
    sh (Func f x b) = iFunc   (printf "(fun (%s %s) %s)") (sh f) (sh x) (sh b)
    sh (MLink a b)  = iMLink  (printf "(link %s %s)") (sh a) (sh b)
    sh (Seq a b)    = iSeq    (printf "(seq %s %s)") (sh a) (sh b)
    sh (Let x a b)  = iLet    (printf "(let (%s = %s) %s)") (sh x) (sh a) (sh b)
    sh (Or a b)     = iOr     (printf "(or %s %s)") (sh a) (sh b)

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


data Value where
  VNum :: Int -> Value
  VLink :: Value -> Value -> Value
  VClosure :: Pattern a b -> Term b c -> Env Value () a -> Value

instance Show Value where
  show (VNum n) = show n
  show (VLink a b) = printf "(link %s %s)" (show a) (show b)
  show (VClosure _ _ _) = "<FUNCTION>"

data Pattern a b where
  PDecl :: Decl a b -> Pattern a b
  PLink :: Pattern a b -> Pattern a c -> Pattern a (Join b c)

eval :: Term a b -> Env Value () a -> Value
eval t env = fst (run t env)
  where
    run :: Term a b -> Interp Value () Value a b
    run (Refn r) = iRefn id r
    run (Num n)  = iNum VNum n
    
    run (Closed  t) = iClosed  id (run t)
    run (LeftT   t) = iLeft    id (run t)
    run (RightT  t) = iRight   id (run t)
    run (WrapCtx t) = iWrapCtx id (run t)
    
    run (Unop op a) = iUnop applyUnop op (run a) where
      applyUnop :: Unop -> Value -> Value
      applyUnop OpFirst (VLink f r) = f
      applyUnop OpRest  (VLink f r) = r
      applyUnop op arg =
        error $ (printf "Bad argument to op: (%s %s)") (show op) (show arg)
    
    run (Binop op a b) = iBinop applyBinop op (run a) (run b) where
      applyBinop :: Binop -> Value -> Value -> Value
      applyBinop OpPlus (VNum a) (VNum b) = VNum (a + b)
      applyBinop OpMult (VNum a) (VNum b) = VNum (a * b)
      applyBinop OpLink a b = VLink a b
      applyBinop op a b =
        error $ (printf "Bad argument to op: (%s %s %s)")
        (show op) (show a) (show b)

    run (Lambda x b) = \env ->
      (VClosure (termToPatt x) b env, env)
    run (Apply f a) = iApply apply (run f) (run a) where
      apply (VClosure x b env') arg =
        eval b (bindPatt x arg env')
    run (If a b c) = \env ->
      case eval a env of
        VNum 0 -> run c env
        VNum _ -> run b env
        v      -> error $ "Bad argument to if: " ++ show v
    run (Func (Decl f) x b) = \env ->
      let closure = VClosure (termToPatt x) b env'
          env'    = bind f closure env in
      (closure, env')
    run (Seq a b) = iSeq (\a b -> b) (run a) (run b)
    
    termToPatt :: Term a b -> Pattern a b
    termToPatt (Decl d) = PDecl d
    termToPatt (MLink p1 p2) = PLink (termToPatt p1) (termToPatt p2)

    bindPatt :: Pattern a b -> Value -> Env Value s a -> Env Value s b
    bindPatt (PDecl d) v env = bind d v env
    bindPatt (PLink p q) (VLink a b) env =
      joinEnv (bindPatt p a env) (bindPatt q b env)
    bindPatt _ _ env = error "Match error"
