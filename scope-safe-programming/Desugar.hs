{-# LANGUAGE GADTs #-}

module Desugar (desugar) where

import Term
import Control.Monad (liftM, liftM2, liftM3, liftM4)

desugar = ds

ds :: Expr a -> IO (Expr a)
ds (Refn r)         = return (Refn r)
ds (Num n)          = return (Num n)
ds (Unop op a)      = liftM2 Unop   (return op) (ds a)
ds (Binop op a b)   = liftM3 Binop  (return op) (ds a) (ds b)
ds (Apply a b)      = liftM2 Apply  (ds a) (ds b)
ds (Lambda x b)     = liftM2 Lambda (return x) (ds b)
ds (IfCase a x b c) = liftM4 IfCase (ds a) (return x) (ds b) (ds c)
ds (Stmt b)         = liftM  Stmt   (dsStmt b)
ds (Let x a b) =
  liftM2 Apply (liftM2 Lambda (return x) (ds b)) (ds a)
ds (If a b c) =
  liftM4 IfCase (ds a) (return $ PNum 0) (ds c) (ds b)
ds (Or a b) = do
  a <- ds a
  b <- ds b
  FreshPatt pX <- pDecl "x"
  let rX = refn "x"
  t <- return $ makeContext $
    tLet (patt pX) (hole a)
      (tIf (expr rX) (expr rX) (hole b))
  ds t
ds (Match a cs) = do
  FreshPatt pX <- pDecl "x"
  let rX = refn "x"
  t <- return $ makeContext $
       tLet (patt pX) (hole a) (dsMatch rX cs)
  ds t
  where
    dsMatch :: OpenExpr a -> Cases p -> Ctx a a p
    dsMatch rX (Else a) = hole a
    dsMatch rX (Case patt thn els) =
      tIfCase (expr rX) (pattHole patt) (hole thn) (dsMatch rX els)

ds (ELeft t)  = liftM ELeft  (ds t)
ds (ERight t) = liftM ERight (ds t)
ds (ECtx t)   = liftM ECtx   (ds t)

dsStmt :: Stmt a b -> IO (Stmt a b)
dsStmt (End a)           = liftM  End    (ds a)
dsStmt (Define x a b)    = liftM3 Define (return x) (ds a) (dsStmt b)
dsStmt (Module ex mod b) = liftM3 Module (return ex) (dsStmt mod) (dsStmt b)
dsStmt (UseMod im b)     = liftM2 UseMod (return im) (dsStmt b)
dsStmt (Func f x a b)    = liftM4 Func   (return f) (return x) (ds a) (dsStmt b)
