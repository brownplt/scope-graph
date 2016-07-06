{-# LANGUAGE GADTs #-}

module Eval (eval) where


import Scope (runMaybeLeftEnv, runMaybeRightEnv)
import Term
import Text.Printf (printf)

eval = evalBigstep


data Value where
  VNum :: Int -> Value
  VLink :: Value -> Value -> Value
  VClosure :: Patt a b -> Expr b -> Env Value () a -> Value

instance Show Value where
  show (VNum n) = show n
  show (VLink a b) = printf "(link %s %s)" (show a) (show b)
  show (VClosure _ _ _) = "<FUNCTION>"

type InterpEval a b = Interp Value () Value a b


evalBigstep :: Expr () -> Value
evalBigstep t = fst $ eval t (emptyEnv ()) where
  eval :: Expr a -> InterpEval a a
  eval (Refn r) = iRefn id r
  eval (Num n)  = iNum VNum n


  eval (Apply f a) = iApply apply (eval f) (eval a) where

    apply (VClosure x b env') arg =
      case match x arg env' of
        Nothing  -> matchError "Apply" arg x
        Just env -> fst $ eval b env


  eval (Stmt a)  = iStmt  id (evalStmt a)
  eval (Lambda x b) = \env -> (VClosure x b env, env)
  eval (IfCase a x b c) = \env ->
    let arg = fst $ eval a env in
    case match x arg env of
      Nothing   -> eval c env
      Just env' -> (fst $ eval b env', env)

  eval (ELeft  t) = iELeft  id (eval t)
  eval (ERight t) = iERight id (eval t)
  eval (ECtx   t) = iECtx   id (eval t)
  
  eval (Unop op a) = iUnop applyUnop op (eval a) where
    applyUnop :: Unop -> Value -> Value
    applyUnop OpFirst (VLink f r) = f
    applyUnop OpRest  (VLink f r) = r
    applyUnop op arg =
      error $ (printf "Bad argument to op: (%s %s)") (show op) (show arg)
  
  eval (Binop op a b) = iBinop applyBinop op (eval a) (eval b) where
    applyBinop :: Binop -> Value -> Value -> Value
    applyBinop OpPlus (VNum a) (VNum b) = VNum (a + b)
    applyBinop OpMult (VNum a) (VNum b) = VNum (a * b)
    applyBinop OpLink a b = VLink a b
    applyBinop OpEq   (VNum a) (VNum b) = VNum (if a == b then 1 else 0)
    applyBinop op a b =
      error $ (printf "Bad argument to op: (%s %s %s)") (show op) (show a) (show b)
  
  eval _ = error "eval: leftover sugar (or missing case)"

  evalStmt :: Stmt a b -> InterpEval a b
  -- TODO: Cleanup this magic?
--  evalStmt (Module ex mod body) =
--    iModule (\_ _ body -> body) (\env -> (export ex, env)) (evalStmt mod) (evalStmt body)
  evalStmt (Module ex mod body) = \env ->
    let (mod', envMod) = evalStmt mod env
        envEx = export ex envMod in
    evalStmt body envEx
  evalStmt (UseMod im body) = \env ->
    let envIm = inport im env
        (body', envBody) = evalStmt body (joinEnv env envIm) in
    (body', joinEnv env envBody)
  evalStmt (Define x defn body) = \env ->
    let defn' = fst $ eval defn env in
    case match x defn' env of
      Just env' -> evalStmt body env'
      Nothing   -> matchError "Define" defn' x
  evalStmt (Func f x a b) = \env ->
    let closure    = VClosure x a envF'
        envF       = bind f closure env
        envF'      = joinEnv envF envB
        (b', envB) = evalStmt b envF in
    (b', envF')
  evalStmt (End a) = eval a
--  evalStmt _   = error "eval statment: leftover sugar (or missing case)"

  match :: Patt a b -> Value -> Env Value s a -> Maybe (Env Value s b)
  match (PDecl d) v env = Just (bind d v env)
  match (PNum n1) (VNum n2) env | n1 == n2 = Just env
  match (PNum _) _ env = Nothing
  match (PLink p q) (VLink a b) env = do
    envP <- match p a env
    envQ <- match q b env
    return $ joinEnv envP envQ
  match (PLink _ _) _ _ = Nothing
  -- TODO: generalize runLeftEnv, runMaybeLeftEnv to something sensible
  match (PLeft a) v env  = runMaybeLeftEnv  (match a v) env
  match (PRight a) v env = runMaybeRightEnv (match a v) env

matchError :: String -> Value -> Patt a b -> err
matchError caller v p =
  error $ caller ++
  ": argument " ++ show v ++
  " doesn't match pattern " ++ show p
