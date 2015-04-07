{-# LANGUAGE GADTs #-}

import Term
import Scope (bind, emptyEnv, runScoped)

t_omega = fst $ runScoped $ do
  FreshTerm x <- newDecl "x"
  return $ lamb x (appl (refn "x") (refn "x"))

t_open = fst $ runScoped $ return (refn "x") -- error

t_apply = fst $ runScoped $ do
  FreshTerm x <- newDecl "x"
  FreshTerm y <- newDecl "y"
  FreshTerm z <- newDecl "z"
  return $ lamb x (lamb (param y z) (appl (refn "x") (refn "y")))


main = do
  putStrLn $ unhygienicShowTerm t_omega
  putStrLn $ unhygienicShowTerm t_apply
  case t_omega of
    Lamb (Decl d) b ->
      -- cannot put `t_open` or `b` inside `CTerm`.
      let env = bind d (Just (CTerm t_omega)) emptyEnv in
      putStrLn $ unhygienicShowTerm $ fst $ subs env b
