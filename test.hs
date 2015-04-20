{-# LANGUAGE GADTs, Rank2Types #-}

import Term
import Lang
import Control.Monad (liftM, liftM2, liftM3)

t_factorial :: IO FreshTerm
t_factorial = do
  Fresh dF <- decl "f"
  Fresh dX <- decl "x"
  let   rF  = refn "f"
  let   rX  = refn "x"
  makeFreshTerm $
    tFunc dF dX (tIf rX
                 (tBinop OpMult rX (tApply rF (tBinop OpPlus rX (tNum (-1)))))
                 (tNum 0))

{-
    sub (Unop op a)       = iUnop      Unop      op      (sub a)
    sub (Lambda x b)      = iLambda    Lambda    (sub x) (sub b)
    sub (MLink a b)       = iMLink     MLink     (sub a) (sub b)
    sub (Let a b c)       = iLet       Let       (sub a) (sub b) (sub c)
    sub (Or a b)          = iOr        Or        (sub a) (sub b)
    
    sub (Seq a b)         = iSeq       Seq       (sub a) (sub b)
    sub (LetModule a b c) = iLetModule LetModule (sub a) (sub b) (sub c)
    sub (UseModule a b)   = iUseModule UseModule (sub a) (sub b)
    
    sub (Num n)           = iNum       Num       n
    sub (Binop op a b)    = iBinop     Binop     op      (sub a) (sub b)
    sub (Apply a b)       = iApply     Apply     (sub a) (sub b)
    sub (If a b c)        = iIf        If        (sub a) (sub b) (sub c)
    sub (Func a b c)      = iFunc      Func      (sub a) (sub b) (sub c)
-}







t_id :: IO ClosedTerm
t_id = do
  Fresh x <- decl "x"
  makeTerm $
    tLambda x (refn "x")

t_omega :: IO ClosedTerm
t_omega = do
  Fresh x <- decl "x"
  makeTerm $
    tLambda x (tApply (refn "x") (refn "x"))

t_open :: IO ClosedTerm
t_open = makeTerm $ (refn "x") -- error

self_apply :: ClosedTerm -> ClosedTerm
self_apply t = Apply t t

t_apply :: IO ClosedTerm
t_apply = do
  Fresh dx <- decl "x"
  Fresh dy <- decl "y"
  Fresh dz <- decl "z"
  makeTerm $
    tLambda dx
         (tLambda (tMLink dy dz)
               (tApply (refn "x") (refn "y")))

t_let :: IO ClosedTerm
t_let = do
  Fresh dx <- decl "x"
  Fresh dy <- decl "y"
  t_id <- t_id
  makeTerm $
    tLet dx (tLambda dy (refn "y")) (refn "x")

t_or :: IO ClosedTerm
t_or = do
  Fresh dx <- decl "x"
  let   rx =  refn "x"
  makeTerm $
    tLambda dx (tOr rx rx)

t_module :: IO ClosedTerm
t_module = do
  Fresh ex <- tExport "x"
  Fresh im <- tImport "x"
  Fresh dx       <- decl "x"
  Fresh df       <- decl "f"
  let rf         =  refn "f"
  let rx         =  refn "x"
  makeTerm $ tBlock $
    tSeq
      (tDefModule ex
        (tSeq (tFunc df dx rx) (tEnd (tApply rf (tNum 3)))))
      (tEnd (tUseModule im rf))

t_subst :: IO ClosedTerm
t_subst = do
  t_omega <- t_omega
  case t_omega of
    Lambda (Decl d) b -> do
      let env = bind d (Just t_omega) (emptyEnv ())
      return $ Lambda (Decl d) (subst env b)

desugar_let :: Term a b -> Term a b
desugar_let (Let x a b) = Apply (Lambda x b) a
--desugar_let (Let x a b) = Apply (Lambda x a) b -- error!

desugar :: Term a b -> IO (Term a b)
desugar (Decl x)     = return $ Decl x
desugar (Refn x)     = return $ Refn x
desugar (Closed t)   = liftM  Closed  (desugar t)
desugar (RightT t)   = liftM  RightT  (desugar t)
desugar (LeftT t )   = liftM  LeftT   (desugar t)
desugar (WrapCtx t)  = liftM  WrapCtx (desugar t)
desugar (Apply a b)  = liftM2 Apply   (desugar a) (desugar b)
desugar (Lambda x b) = liftM2 Lambda  (desugar x) (desugar b)
desugar (MLink a b)  = liftM2 MLink   (desugar a) (desugar b)
desugar (If a b c)   = liftM3 If      (desugar a) (desugar b) (desugar c)
desugar (Let x a b)  =
  liftM2 Apply (liftM2 Lambda (desugar x) (desugar b)) (desugar a)
desugar (Or a b) = do
  a <- desugar a
  b <- desugar b
  Fresh dx <- decl "x"
  let   rx =  refn "x"
  t <- makeContext $
    tLet (term dx) (hole a)
      (tIf (term rx) (term rx) (hole b))
  desugar t


putTerm = putStrLn . show

main = do
  t_omega <- t_omega
  t_apply <- t_apply
  t_let <- t_let
  t_id <- t_id
  t_or <- t_or
  t_module <- t_module
  t_subst <- t_subst
--  t_open <- t_open
  
  putTerm t_omega
  putTerm t_apply
  
  putStrLn ""
  putTerm $ t_or
  putStrLn "==>"
  t_or_core <- desugar t_or
  putTerm $ t_or_core
  
  putStrLn ""
  putStrLn "A big term:"
  putTerm $ self_apply $ t_or_core
  
  putStrLn ""
  putStrLn "Unimpressive subst:"
  putTerm $ t_subst

  putStrLn ""
  putStrLn "Modules:"
  putTerm $ t_module
  
  putStrLn ""
  putStrLn "ok"
