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
  
