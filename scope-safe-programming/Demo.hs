{-# LANGUAGE GADTs #-}

import Scope

data Expr a where
  Id   :: Refn a             -> Expr a
  Lamb :: Decl a b -> Expr b -> Expr a
  App  :: Expr a   -> Expr a -> Expr a

idExpr :: IO (Expr ())
idExpr = do
  NewDecl xd s <- decl "x" emptyScope
  let xr = refn "x" s
  return (Lamb xd (Id xr))

data Value where
  Closure :: Decl a b -> Expr b -> Env Value () a
          -> Value

eval :: Expr a -> Env Value () a -> Value
eval (Id xr) env = find xr env
eval (Lamb xd body) env = Closure xd body env
-- Try using the wrong env here: the code won't typecheck
eval (App func arg) env =
  case eval func env of
    Closure xd body env' ->
      let argVal = eval arg env in
      eval body (bind xd argVal env')

main = do
  putStrLn "ok"
