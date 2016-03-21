import string-dict as D

import my-gdrive("sugar/scope-rule.arr") as R
import my-gdrive("sugar/term.arr") as T
import my-gdrive("sugar/scope.arr") as S
include my-gdrive("sugar/util.arr")



core-lang-scope-rules = [D.mutable-string-dict:]
arities = [D.mutable-string-dict:]

fun add-to-core(con, arity, lst):
  core-lang-scope-rules.set-now(con, R.make-rule(arity, lst))
  arities.set-now(con, arity)
end

fun add-to-surface(con, arity):
  arities.set-now(con, arity)
end

lt = R.lt
top = R.top
bot = R.bot
child = R.child
fact = R.fact
constraint = S.constraint

# Core Language
add-to-core("Apply", 2, [list:])
add-to-core("Arg", 2, [list:])
add-to-core("EndArgs", 0, [list:])
add-to-core("Lambda", 2, [list:
    lt(child(1), child(0))
  ])
add-to-core("Param", 2, [list:
    lt(bot, child(0)),
    lt(bot, child(1))
  ])
add-to-core("EndParams", 0, [list:])
add-to-core("Plus", 2, [list:])

# Surface Language for example 1
add-to-surface("Let1", 3)

# Surface 
add-to-surface("Let*", 2)
add-to-surface("Bind*", 3)
add-to-surface("EndBinds", 0)



check "Constraint Generation":
  lhs = T.parse-term("(P (Q a b) c)")
  rhs = T.parse-term("(R a (S b c))")
  
  cs = S.gen-constraints(lhs, rhs)
  # Constraint generation example from the paper
  # (In an arbitrary order, and with 0-based numbers instead of 1-based)
  cs is [list:
    constraint(
      [list: fact("P", bot, child(1))],
      [list: fact("R", bot, child(1)), fact("S", bot, child(1))]), 
    constraint(
      [list: fact("P", bot, child(0)), fact("Q", bot, child(1))],
      [list: fact("R", bot, child(1)), fact("S", bot, child(0))]), 
    constraint(
      [list: fact("P", bot, child(0)), fact("Q", bot, child(0))],
      [list: fact("R", bot, child(0))]), 
    constraint(
      [list: fact("P", child(1), top)],
      [list: fact("R", child(1), top), fact("S", child(1), top)]), 
    constraint(
      [list: fact("P", child(1), child(0)), fact("Q", bot, child(1))],
      [list: fact("S", child(1), child(0))]), 
    constraint(
      [list: fact("P", child(1), child(0)), fact("Q", bot, child(0))],
      [list: fact("R", child(1), child(0)), fact("S", child(1), top)]), 
    constraint(
      [list: fact("P", child(0), top), fact("Q", child(1), top)],
      [list: fact("R", child(1), top), fact("S", child(0), top)]), 
    constraint(
      [list: fact("P", child(0), child(1)), fact("Q", child(1), top)],
      [list: fact("S", child(0), child(1))]), 
    constraint(
      [list: fact("Q", child(1), child(0))],
      [list: fact("R", child(1), child(0)), fact("S", child(0), top)]), 
    constraint(
      [list: fact("P", child(0), top), fact("Q", child(0), top)],
      [list: fact("R", child(0), top)]), 
    constraint(
      [list: fact("P", child(0), child(1)), fact("Q", child(0), top)],
      [list: fact("R", child(0), child(1)), fact("S", bot, child(1))]), 
    constraint(
      [list: fact("Q", child(0), child(1))],
      [list: fact("R", child(0), child(1)), fact("S", bot, child(0))])]
end


check "Resugaring Scope Example 1":
  lhs = T.parse-term("(Let1 a b c)")
  rhs = T.parse-term("(Apply (Lambda a c) b)")
  
  cs = S.gen-constraints(lhs, rhs)
  rules = S.solve-constraints(arities, core-lang-scope-rules, cs)
  
  let1-rule = rules.get-value-now("Let1")
  rule = let1-rule
  rule.lt(child(0), top) is true
  rule.lt(child(1), top) is true
  rule.lt(child(2), top) is true
  rule.lt(bot, child(0)) is false
  rule.lt(bot, child(1)) is false
  rule.lt(bot, child(2)) is false
  rule.lt(child(0), child(1)) is false
  rule.lt(child(0), child(2)) is false
  rule.lt(child(1), child(0)) is false
  rule.lt(child(1), child(2)) is false
  rule.lt(child(2), child(0)) is true
  rule.lt(child(2), child(1)) is false
  
  print(rules)
end

check "Resugaring Scope Example 2":
  
  lhs1 = T.parse-term("(Let* (EndBinds) d)")
  rhs1 = T.parse-term("d")
  
  lhs2 = T.parse-term("(Let* (Bind* a b c) d)")
  rhs2 = T.parse-term("(Apply (Lambda a (Let* c d)) b)")
  
  sugar = [list: pair(lhs1, rhs1), pair(lhs2, rhs2)]
  
  rules = S.resugar-scope(sugar, arities, core-lang-scope-rules)
  print("Rules:")
  print(rules)
end



## check "Scope":
##
##   t = T.parse-term("(Lambda (Param &x (Param &y (EndParams))) (Plus $x       
##   $y))")
##
##   scope = S.compute-var-scope(core-lang-scope-rules, t)
##
##   xD = S.make-in-port(t.get(0).get(0))
##   yD = S.make-in-port(t.get(0).get(1).get(0))
##   xR = S.make-in-port(t.get(1).get(0))
##   yR = S.make-in-port(t.get(1).get(1))
##
##   scope.less-than(xR, xD) is true
##   scope.less-than(yR, xD) is true
##   scope.less-than(xR, yD) is true
##   scope.less-than(yR, yD) is true
##
##   scope.less-than(xD, yD) is false
##   scope.less-than(yD, xD) is false
##
##   scope.less-than(xD, xR) is false
##   scope.less-than(xD, yR) is false
##   scope.less-than(yD, xR) is false
##   scope.less-than(yD, yR) is false
## end
##
## check "Binding":
##
##   t = T.parse-term(
##     "(Lambda &x (Lambda (Param &x (Param &y (EndParams))) (Plus $x           
##     $y)))")
##
##   binds = S.compute-bindings(core-lang-scope-rules, t)
##
##   x1D = t.get(0)
##   x2D = t.get(1).get(0).get(0)
##   yD  = t.get(1).get(0).get(1).get(0)
##   xR  = t.get(1).get(1).get(0)
##   yR  = t.get(1).get(1).get(1)
##
##   binds.member(S.bind(xR, [list: x2D])) is true
##   binds.member(S.bind(yR, [list: yD])) is true
## end










