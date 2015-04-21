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

{-
eval_bigstep :: Expr () -> Value
eval_bigstep t = eval t (emptyEnv ())
  where
    eval :: Term a b -> Env Value () a -> Value
    eval t env = fst (run t env)

    run (If a b c) = \env ->
      case eval a env of
        VNum 0 -> run c env
        VNum _ -> run b env
        v      -> error $ "Bad argument to if: " ++ show v
    run (Func f x b) = \env ->
      let closure = VClosure (termToPatt x) b env'
          env'    = bind f closure env in
      (closure, env')
    run (Block a) = iBlock id (runBlock a)
    
    runBlock :: Block a b -> Interp Value () Value a b
    runBlock (Seq a b) = iSeq (\a b -> b) (run a) (runBlock b)
    runBlock (End a)   = run a
-}

{-
subst :: Env (Maybe ClosedExpr) () a -> Term a b -> Term a b
--subst :: Env (Maybe (Term a a)) () b -> Term b b -> Term a a
subst env t = fst $ sub t env
  where
    sub :: Term a b -> Interp (Maybe ClosedTerm) () (Term a b) a b
--    sub :: Term b b -> Interp (Maybe (Term a a)) () (Term a a) b b
    sub (Decl d) = \env ->
      let (d', env') = subDecl d env in
      (Decl d', env')
    sub (Refn r) = iRefn subRefn r where
      subRefn Nothing  = Refn r
      subRefn (Just t) = Closed t
    sub (Import im) = \env -> (Import im, inport im env)
    sub (Export ex) = \env -> (Export ex, export ex env)

    sub (Closed  t) = iClosed  Closed  (sub t)
    sub (LeftT   t) = iLeft    LeftT   (sub t)
    sub (RightT  t) = iRight   RightT  (sub t)
    sub (WrapCtx t) = iWrapCtx WrapCtx (sub t)

    sub (Num n)         = iNum       Num       n
    sub (Unop op a)     = iUnop      Unop      op      (sub a)
    sub (Binop op a b)  = iBinop     Binop     op      (sub a) (sub b)
    sub (DefModule a b) = iDefModule DefModule (sub a) (subBlock b)
    sub (UseModule a b) = iUseModule UseModule (sub a) (sub b)
    sub (Lambda x b)    = iLambda    Lambda    (sub x) (sub b)
    sub (Apply a b)     = iApply     Apply     (sub a) (sub b)
    sub (If a b c)      = iIf        If        (sub a) (sub b) (sub c)
    sub (Func a b c)    = iFunc      Func      (subDecl a) (sub b) (sub c)
    sub (MLink a b)     = iMLink     MLink     (sub a) (sub b)
    sub (Let a b c)     = iLet       Let       (sub a) (sub b) (sub c)
    sub (Block a)       = iBlock     Block     (subBlock a)
    sub (Or a b)        = iOr        Or        (sub a) (sub b)
    
    subBlock :: Block a b -> Interp (Maybe ClosedTerm) () (Block a b) a b
    subBlock (Seq a b)  = iSeq Seq (sub a) (subBlock b)
    subBlock (End a)    = iEnd End (sub a)

    subDecl :: Decl a b -> Interp (Maybe ClosedTerm) () (Decl a b) a b
    subDecl d = \env -> (d, bind d Nothing env)
-}
