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
