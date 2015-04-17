module Interp where

import Scope

type Interp v s r a b = Env v s a -> (r, Env v s b)

joinInterp :: (r1 -> r2 -> r3)
        -> Interp v s r1 a b
        -> Interp v s r2 a c
        -> Interp v s r3 a (Join b c)
joinInterp f i1 i2 env =
  let (r1, env1) = i1 env
      (r2, env2) = i2 (setState env (getState env1)) in
  (f r1 r2, join env1 env2)

produce :: r -> Interp v s r a a
produce ret env = (ret, env)


runScoped1 :: (t1 -> t2)
              -> Scoped a b t1
              -> Scoped a a t2
runScoped1 f ab a = let (t1, b) = ab a in (f t1, a)

runScoped2 :: (t1 -> t2 -> t3)
              -> Scoped a b t1
              -> Scoped b c t2
              -> Scoped a a t3
runScoped2 f ab bc a =
  let (t1, b) = ab a
      (t2, c) = bc b in
  (f t1 t2, a)

runScoped3 :: (t1 -> t2 -> t3 -> t4)
              -> Scoped a b t1
              -> Scoped b c t2
              -> Scoped c d t3
              -> Scoped a a t4
runScoped3 f ab bc cd a =
  let (t1, b) = ab a
      (t2, c) = bc b
      (t3, d) = cd c in
  (f t1 t2 t3, a)

runInterp1 :: (r1 -> r2)
              -> Interp v s r1 a b
              -> Interp v s r2 a a
runInterp1 f ab a =
  let (r1, b) = ab a in
  (f r1, a)

runInterp2 :: (r1 -> r2 -> r3)
              -> Interp v s r1 a b
              -> Interp v s r2 b c
              -> Interp v s r3 a a
runInterp2 f ab bc a =
  let (r1, b) = ab a
      (r2, c) = bc b in
  (f r1 r2, a)

runInterp3 :: (r1 -> r2 -> r3 -> r4)
              -> Interp v s r1 a b
              -> Interp v s r2 b c
              -> Interp v s r3 c d
              -> Interp v s r4 a a
runInterp3 f ab bc cd a =
  let (r1, b) = ab a
      (r2, c) = bc b
      (r3, d) = cd c in
  (f r1 r2 r3, a)