{-# LANGUAGE GADTs, FlexibleInstances #-}

module Show () where

import Term
import Data.Char (ord, chr)
import Text.Printf (printf)


data ShowState = ShowState Char String -- next var, current module name

type InterpShow a b = Interp String ShowState String a b


initEnv :: Env String ShowState ()
initEnv = emptyEnv (ShowState 'a' "%TOPLEVEL_MODULE")

instance Show ClosedExpr  where show t = fst $ sh t initEnv
instance Show ClosedStmt  where show t = fst $ shStmt t initEnv

sh :: Expr a -> InterpShow a a
sh (Refn r)       = iRefn id r
sh (Num n)        = iNum show n
sh (Unop op a)    = iUnop   (printf "(%s %s)")     (show op) (sh a)
sh (Binop op a b) = iBinop  (printf "(%s %s %s)")  (show op) (sh a) (sh b)
sh (Lambda x b)   = iLambda (printf "(lam %s %s)") (shPatt x) (sh b)
sh (Apply f a)    = iApply  (printf "(%s %s)")     (sh f) (sh a)
sh (Stmt a)       = iStmt   (printf "(block%s)")   (shStmt a)
sh (If a b c)     = iIf     (printf "(if %s %s %s)") (sh a) (sh b) (sh c)
sh (Let x a b)    = iLet    (printf "(let (%s = %s) %s)") (shPatt x) (sh a) (sh b)
sh (Or a b)       = iOr     (printf "(or %s %s)") (sh a) (sh b)
sh (Match a b)    = iMatch  (printf "(match %s %s)") (sh a) (shCase b)
sh (IfCase a x b c)=iIfCase (printf "(if-case %s %s %s %s)") (sh a) (shPatt x) (sh b) (sh c)
sh (ELeft   t)    = iELeft   id (sh t)
sh (ERight  t)    = iERight  id (sh t)
sh (ECtx    t)    = iECtx    id (sh t)

shStmt :: Stmt a b -> InterpShow a b
shStmt (End a)           = sh a
shStmt (Func f x a b)    = iFunc   (printf " (fun (%s %s) %s)%s")
                           (shDecl f) (shPatt x) (sh a) (shStmt b)
shStmt (Define x a b)    = iDefine (printf " (define %s %s)%s")
                           (shPatt x) (sh a) (shStmt b)
shStmt (Module ex mod b) = iModule (printf " (module %s%s)%s")
                           (shExport ex) (shStmt mod) (shStmt b)
shStmt (UseMod im b)     = iUseMod (printf " (import %s %s)%s")
                           (shImport im) (shStmt b)

shPatt :: Patt a b -> InterpShow a b
shPatt (PDecl d)   = shDecl d
shPatt (PNum n)    = iPNum (show n)
shPatt (PLink a b) = iPLink (printf "(link %s %s)") (shPatt a) (shPatt b)
shPatt (PLeft a)   = iPLeft  id (shPatt a)
shPatt (PRight a)  = iPRight id (shPatt a)

shCase :: Cases a -> InterpShow a a
shCase (Else a) = sh a
shCase (Case x a b) = iCase (printf "(case %s %s) %s")
                      (shPatt x) (sh a) (shCase b)

shDecl :: Decl a b -> InterpShow a b
shDecl d env =
  let (v, newEnv) = nextName env
      name = [v] in
  (name, bind d name newEnv)

shImport :: Import a b -> InterpShow a b
shImport im = \env ->
  let env' = inport im env in
  (getModName env', env')

shExport :: Export a b -> InterpShow a b
shExport ex = \env ->
  let (v, env') = nextModName env in
  ([v], export ex env')

nextName :: Env String ShowState a -> (Char, Env String ShowState a)
nextName env =
  let ShowState oldName mod = getState env
      newName = chr (ord oldName + 1)
      newEnv  = setState env (ShowState newName mod) in
  (oldName, newEnv)

nextModName :: Env String ShowState a -> (Char, Env String ShowState a)
nextModName env =
  let ShowState oldName mod = getState env
      newName = chr (ord oldName + 1)
      newEnv  = setState env (ShowState newName [oldName]) in
  (oldName, newEnv)

getModName :: Env String ShowState a -> String
getModName env =
  let ShowState _ modName = getState env in
  modName
