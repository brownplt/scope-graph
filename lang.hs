{-# LANGUAGE FlexibleInstances #-}

module Lang where

import Term

import Data.Char (ord, chr)


subst :: Env (Maybe ClosedTerm) () a -> Term a b -> Term a b
subst env t = interpret interp_subst t env

interp_subst :: Interpreter (Maybe ClosedTerm) () Term
interp_subst = Interpreter {
  iDecl = \d env -> (Decl d, bind d Nothing env),
  iRefn = \r v ->
    case v of
      Nothing -> Refn r
      Just t  -> Closed t,
  iImpt = \im env -> (Import im, inport im env),
  iExpt = \ex env -> (Export ex, export ex env),
  
  iClosed  = Closed,
  iLeft    = LeftT,
  iRight   = RightT,
  iWrapCtx = WrapCtx,
  
  iLetModule = LetModule,
  iUseModule = UseModule,
  iLambda    = Lambda,
  iApply     = Apply,
  iIf        = If,
  iFunc      = Func,
  iParam     = Param,
  iSeq       = Seq,
  iLet       = Let,
  iOr        = Or,
  iNum       = Num
  }


data ShowState = ShowState Char String -- next var, current module name

interp_show :: SimpleInterpreter String ShowState String
interp_show = SimpleInterpreter {
  sDecl = \d env ->
     let (v, newEnv) = nextName env
         name = [v] in
     (name, bind d name newEnv),
  sRefn = \_ str -> str,
  sImpt = \im env ->
    let env' = inport im env in
    (getModName env', env'),
  sExpt = \ex env ->
    let (v, env') = nextModName env in
    ([v], export ex env'),
  
  sLetModule = \ex mod body ->
    "(let-module (" ++ ex ++ ") " ++ mod ++ " " ++ body ++ ")",
  sUseModule = \im body ->
    "(use-module (" ++ im ++ ") " ++ body ++ ")",
  sLambda = \x b   -> "(lam " ++ x ++ ". " ++ b ++ ")",
  sApply  = \a b   -> "(" ++ a ++ " " ++ b ++ ")",
  sIf     = \a b c -> "(if " ++ a ++ " " ++ b ++ " " ++ c ++ ")",
  sFunc   = \f x b -> "(fun (" ++ f ++ " " ++ x ++ ") " ++ b ++ ")",
  sParam  = \a b   -> a ++ " " ++ b,
  sSeq    = \a b   -> a ++ " " ++ b,
  sLet    = \x a b -> "(let " ++ x ++ " " ++ a ++ " " ++ b ++ ")",
  sOr     = \a b   -> "(or " ++ a ++ " " ++ b ++ ")",
  sNum    = \n     -> show n
  }
  where
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


instance Show ClosedTerm where
  show t = show $ simpleInterpret interp_show t (emptyEnv init)
    where init = ShowState 'a' "%TOPLEVEL_MODULE"
