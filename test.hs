{-# LANGUAGE GADTs, Rank2Types #-}

import Term
import Scope (bind, emptyEnv, Join,
              emptyScope) -- TODO: remove
import Control.Monad (liftM, liftM2, liftM3)

t_id :: IO (Term () ())
t_id = do
  Fresh x <- decl "x"
  makeTerm $
    lamb x (refn "x")

t_omega :: IO (Term () ())
t_omega = do
  Fresh x <- decl "x"
  makeTerm $
    lamb x (appl (refn "x") (refn "x"))

t_open :: IO (Term () ())
t_open = makeTerm $ (refn "x") -- error

t_apply :: IO (Term () ())
t_apply = do
  Fresh dx <- decl "x"
  Fresh dy <- decl "y"
  Fresh dz <- decl "z"
  makeTerm $
    lamb dx
         (lamb (param dy dz)
               (appl (refn "x") (refn "y")))

t_let :: IO (Term () ())
t_let = do
  Fresh dx <- decl "x"
  Fresh dy <- decl "y"
  t_id <- t_id
  makeTerm $
    tlet dx (lamb dy (refn "y")) (refn "x")

t_or :: IO (Term () ())
t_or = do
  Fresh dx <- decl "x"
  let   rx =  refn "x"
  makeTerm $
    lamb dx (tor rx rx)

desugar_let :: Term a b -> Term a b
desugar_let (Let x a b) = Apply (Lambda x b) a
--desugar_let (Let x a b) = Apply (Lambda x a) b -- error!

hole = tright
term = tleft

desugar :: Term a b -> IO (Term a b)
desugar (Decl x)     = return $ Decl x
desugar (Refn x)     = return $ Refn x
desugar (Closed t)   = liftM  Closed (desugar t)
desugar (RightT t)   = liftM  RightT (desugar t)
desugar (LeftT t )   = liftM  LeftT  (desugar t)
desugar (Apply a b)  = liftM2 Apply  (desugar a) (desugar b)
desugar (Lambda x b) = liftM2 Lambda (desugar x) (desugar b)
desugar (Param a b)  = liftM2 Param  (desugar a) (desugar b)
desugar (If a b c)   = liftM3 If     (desugar a) (desugar b) (desugar c)
desugar (Let x a b)  =
  liftM2 Apply (liftM2 Lambda (desugar x) (desugar b)) (desugar a)
desugar (Or a b) = do
  a <- desugar a
  b <- desugar b
  Fresh dx <- decl "x"
  let   rx =  refn "x"
  makeContext $
    tlet (term dx) (hole a)
      (tif (term rx) (term rx) (hole b))


showTerm = putStrLn . unhygienicShowTerm

main = do
  t_omega <- t_omega
  t_apply <- t_apply
  t_let <- t_let
  t_id <- t_id
  t_or <- t_or
--  t_open <- t_open
  showTerm t_omega
  showTerm t_apply
  (case t_omega of
    Lambda (Decl d) b ->
      -- cannot put `t_open` or `b` inside `CTerm`.
      let env = bind d (Just t_apply) emptyEnv in do
      showTerm $ fst $ subs env b) :: IO ()
  showTerm $ desugar_let t_let
  
  putStrLn ""
  showTerm $ t_or
  putStrLn "==>"
  t_or_core <- desugar t_or
  showTerm $ fst $ subs emptyEnv t_or_core
  
  putStrLn ""
  putStrLn "ok"
