{-# LANGUAGE GADTs #-}

import Term
import Show
import Eval
import Desugar

tLink a b = tBinop OpLink a b

t_funcs :: IO FreshStmt
t_funcs = do
  FreshDecl dFact <- decl "fact"
  FreshDecl dSum  <- decl "sum"
  FreshPatt pX    <- pDecl "x"
  FreshPatt pY    <- pDecl "y"
  let rX = refn "x"
      rY = refn "y"
      rFact = refn "fact"
      rSum  = refn "sum"
  return $ makeFreshStmt $
    tFunc dFact pX (tIf (tBinop OpEq rX (tNum 0))
                    (tNum 1)
                    (tBinop OpMult rX
                     (tApply rFact
                      (tBinop OpPlus rX (tNum (-1))))))
    (tFunc dSum pX (tMatch rX
                    (tCase (tPLink pX pY)
                       (tBinop OpPlus (tApply rSum rX) (tApply rSum rY))
                    (tCase pX
                       rX
                    (tElse
                       (tNum 0)))))
     (tEnd (tBinop OpPlus
            (tApply rFact (tNum 5))
            (tApply rSum (tLink (tLink (tNum 3) (tNum 4)) (tNum 5))))))

t_test :: IO ClosedExpr
t_test = do
  FreshStmt t_funcs <- t_funcs
  return (Stmt t_funcs)

putExpr = putStrLn . show

runTest :: IO ClosedExpr -> IO ()
runTest t = do
  putStrLn ""
  t <- t
  putExpr t
  t <- desugar t
  putStrLn "==>"
  putExpr t
  putStrLn $ "->* " ++ show (eval t)

main = do
  runTest t_test
  

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




{-


t_id :: IO ClosedExpr
t_id = do
  Fresh x <- decl "x"
  makeExpr $
    tLambda x (refn "x")

t_omega :: IO ClosedExpr
t_omega = do
  Fresh x <- decl "x"
  makeExpr $
    tLambda x (tApply (refn "x") (refn "x"))

t_open :: IO ClosedExpr
t_open = makeExpr $ (refn "x") -- error

self_apply :: ClosedExpr -> ClosedExpr
self_apply t = Apply t t

t_apply :: IO ClosedExpr
t_apply = do
  Fresh dx <- decl "x"
  Fresh dy <- decl "y"
  Fresh dz <- decl "z"
  makeExpr $
    tLambda dx
         (tLambda (tMLink dy dz)
               (tApply (refn "x") (refn "y")))

t_let :: IO ClosedExpr
t_let = do
  Fresh dx <- decl "x"
  Fresh dy <- decl "y"
  t_id <- t_id
  makeExpr $
    tLet dx (tLambda dy (refn "y")) (refn "x")

t_or :: IO ClosedExpr
t_or = do
  Fresh dx <- decl "x"
  let   rx =  refn "x"
  makeExpr $
    tLambda dx (tOr rx rx)

t_module :: IO ClosedExpr
t_module = do
  Fresh ex <- tExport "x"
  Fresh im <- tImport "x"
  Fresh dx       <- decl "x"
  Fresh df       <- decl "f"
  let rf         =  refn "f"
  let rx         =  refn "x"
  makeExpr $ tBlock $
    tSeq
      (tDefModule ex
        (tSeq (tFunc df dx rx) (tEnd (tApply rf (tNum 3)))))
      (tEnd (sUseMod im rf))

t_subst :: IO ClosedExpr
t_subst = do
  t_omega <- t_omega
  case t_omega of
    Lambda (PDecl d) b -> do
      let env = bind d (Just t_omega) (emptyEnv ())
      return $ Lambda (PDecl d) (subst env b)

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

-}