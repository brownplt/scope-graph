{-# LANGUAGE GADTs, Rank2Types, ScopedTypeVariables, ImpredicativeTypes #-}

import Term
import Scope (bind, emptyEnv, Scope)

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

main = do
  t_omega <- t_omega
  t_apply <- t_apply
--  t_open <- t_open
  putStrLn $ unhygienicShowTerm t_omega
  putStrLn $ unhygienicShowTerm t_apply
  case t_omega of
    Lamb (Decl d) b ->
      -- cannot put `t_open` or `b` inside `CTerm`.
      let env = bind d (Just t_apply) emptyEnv in do
      putStrLn $ unhygienicShowTerm $ fst $ subs env b
  putStrLn "ok"
