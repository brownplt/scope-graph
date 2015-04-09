{-# LANGUAGE GADTs #-}

import Term
import Scope (bind, emptyEnv, Scope, Split)

t_id :: IO (Term () ())
t_id = do
  FreshDecl x <- decl "x"
  makeTerm $
    lamb x (refn "x")

t_omega :: IO (Term () ())
t_omega = do
  FreshDecl x <- decl "x"
  makeTerm $
    lamb x (appl (refn "x") (refn "x"))

t_open :: IO (Term () ())
t_open = makeTerm $ (refn "x") -- error

t_apply :: IO (Term () ())
t_apply = do
  FreshDecl dx <- decl "x"
  FreshDecl dy <- decl "y"
  FreshDecl dz <- decl "z"
  makeTerm $
    lamb dx
         (lamb (param dy dz)
               (appl (refn "x") (refn "y")))

t_let = do
  FreshDecl dx <- decl "x"
  FreshDecl dy <- decl "y"
  t_id <- t_id
  makeTerm $
    tlet dx (lamb dy (refn "y")) (refn "x")

desugar_let :: Term a b -> Term a b
desugar_let (Let x a b) = Apply (Lambda x b) a
--desugar_let (Let x a b) = Apply (Lambda x a) b -- error!
desugar_let t = t

showTerm = putStrLn . unhygienicShowTerm

main = do
  t_omega <- t_omega
  t_apply <- t_apply
  t_let <- t_let
--  t_open <- t_open
  showTerm t_omega
  showTerm t_apply
  case t_omega of
    Lambda (Decl d) b ->
      -- cannot put `t_open` or `b` inside `CTerm`.
      let env = bind d (Just t_apply) emptyEnv in do
      showTerm $ fst $ subs env b
  showTerm $ desugar_let t_let
  putStrLn "ok"
