module Interp where

import Scope

type Interp v s r a b = Env v s a -> (r a b, Env v s b)

joinInterp :: (r a b -> r a c -> r a (Join b c))
        -> Interp v s r a b
        -> Interp v s r a c
        -> Interp v s r a (Join b c)
joinInterp f i1 i2 env =
  let (r1, env1) = i1 env
      (r2, env2) = i2 (setState env (getState env1)) in
  (f r1 r2, join env1 env2)

produce :: r a a -> Interp v s r a a
produce ret env = (ret, env)


runScoped1 :: (t1 -> t2)
              -> Scoped a a t1
              -> Scoped a a t2
runScoped1 f a s =
  (f (fst $ a s), s)

runScoped2 :: (t1 -> t2 -> t3)
              -> Scoped a a t1
              -> Scoped a a t2
              -> Scoped a a t3
runScoped2 f a b s =
  (f (fst $ a s) (fst $ b s), s)

runScoped3 :: (t1 -> t2 -> t3 -> t4)
              -> Scoped a a t1
              -> Scoped a a t2
              -> Scoped a a t3
              -> Scoped a a t4
runScoped3 f a b c s =
  (f (fst $ a s) (fst $ b s) (fst $ c s), s)

runInterp1 :: (r a a -> r a a)
              -> Interp v s r a a
              -> Interp v s r a a
runInterp1 f a env =
  (f (fst $ a env), env)

runInterp2 :: (r a a -> r a a -> r a a)
              -> Interp v s r a a
              -> Interp v s r a a
              -> Interp v s r a a
runInterp2 f a b env =
  (f (fst $ a env) (fst $ b env), env)

runInterp3 :: (r a a -> r a a -> r a a -> r a a)
              -> Interp v s r a a
              -> Interp v s r a a
              -> Interp v s r a a
              -> Interp v s r a a
runInterp3 f a b c env =
  (f (fst $ a env) (fst $ b env) (fst $ c env), env)
