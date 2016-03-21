provide *
provide-types *

import string-dict as D
import my-gdrive("sugar/preorder.arr") as P


data Elem:
  | top
  | bot
  | child(i :: Number)
sharing:
  to-preorder-key(self):
    cases(Elem) self:
      | top => "top"
      | bot => "bot"
      | child(i) => tostring(i)
    end
  end,
  show(self):
    cases(Elem) self:
      | top => "⊤"
      | bot => "⊥"
      | child(i) => tostring(i)
    end
  end
end

fun string-to-elem(str):
  if str == "top":
    top
  else if str == "bot":
    bot
  else:
    cases(Option) string-to-number(str):
      | some(i) => child(i)
      | none    => raise("scope-rule/string-to-elem: invalid string")
    end
  end
end

data Lt:
  | lt(left :: Elem, right :: Elem)
sharing:
  to-preorder-edge(self):
    P.edge(self.left.to-preorder-key(), self.right.to-preorder-key())
  end
end

# A scoping rule
data Rule:
  | mk-rule(order :: P.Preorder)
sharing:
  lt(self, left :: Elem, right :: Elem):
    self.order.less-than(left.to-preorder-key(), right.to-preorder-key())
  end,
  to-list(self) -> List<Lt>:
    for map(edge from self.order.to-list()):
      lt(string-to-elem(edge.a), string-to-elem(edge.b))
    end
  end
end

fun make-rule(arity :: Number, lst :: List<Lt>) -> Rule:
  #TODO: check that order is valid (all 0<x<n & 0 least & n+1 greatest)
  # Add lexical scope (technically, this is optional)
  shadow lst =
    for fold(shadow lst from lst, i from range(0, arity)):
      l = lt(child(i), top)
      if not(lst.member(l)): link(l, lst)
      else:                  lst
      end
    end
  l = lt(bot, top)
  shadow lst =
    if not(lst.member(l)): link(l, lst)
    else:                  lst
    end
  # Initialize based on lst
  nodes = [list: top, bot] + map(child, range(0, arity))
  shadow nodes = nodes.map(_.to-preorder-key())
  edges = lst.map(_.to-preorder-edge())
  order = P.preorder(nodes, edges)
  # Take transitive closure (important; used in proof)
  shadow order = order.transitive-closure()
  mk-rule(order)
end

# A set of scoping rules (capital Sigma)
type RuleSet = D.MutableStringDict<Rule>

data Fact:
  | fact(con :: String, left :: Elem, right :: Elem)
sharing:
  show(self):
    self.con + ": " + self.left.show() + " <* " + self.right.show()
  end
end

fun rules-to-facts(rs :: RuleSet) -> List<Fact>:
  for fold(facts from [list:], con from rs.keys-now().to-list()):
    rule = rs.get-value-now(con)
    rule-facts = for map(x from rule.to-list()):
      fact(con, x.left, x.right)
    end
    facts + rule-facts
  end
end

fun facts-to-rules(arities :: D.MutableStringDict<Number>, facts :: List<Fact>) -> RuleSet:
  d = [D.mutable-string-dict:]
  for each(con from arities.keys-now().to-list()):
    d.set-now(con, [list:])
  end
  for each(f from facts):
    d.set-now(f.con,
      link(
        lt(f.left, f.right),
        d.get-value-now(f.con)))
  end
  for each(con from d.keys-now().to-list()):
    d.set-now(con, make-rule(arities.get-value-now(con), d.get-value-now(con)))
  end
  d
end

check:
  r-lambda = make-rule(2, [list: lt(child(1), child(0))])
  r-lambda.lt(child(0), top) is true
  r-lambda.lt(child(1), top) is true
  r-lambda.lt(child(1), child(0)) is true
  r-lambda.lt(top, child(0)) is false
  r-lambda.lt(top, child(1)) is false
  r-lambda.lt(child(0), child(1)) is false
  
  # Sanity checks (not real tests) on rules-to-facts and facts-to-rules
  facts = rules-to-facts([D.mutable-string-dict: "lambda", r-lambda])
  facts.length() is 4
  rules = facts-to-rules([D.mutable-string-dict: "lambda", 2], facts)
  rules.get-value-now("lambda").order.edges.length() is 4
end