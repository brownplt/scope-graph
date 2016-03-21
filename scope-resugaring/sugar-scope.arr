provide *
provide-types *

import string-dict as D
import all from lists
import sets as S

include my-gdrive("sugar/util.arr")
import my-gdrive("sugar/scope-rule.arr") as R
import my-gdrive("sugar/term.arr") as T
import my-gdrive("sugar/preorder.arr") as P


type Port = String

fun make-in-port(t :: T.Term) -> Port:
  "-" + tostring(t.get-id())
end

fun make-out-port(t :: T.Term) -> Port:
  "+" + t.get-id()
end

fun port-to-term-id(id :: Port) -> String:
  string-substring(id, 1, string-length(id))
end

fun lookup-port(t :: T.Term, id :: Port) -> T.Term:
  t.lookup(port-to-term-id(id))
end

fun is-refn-port(id :: Port) -> Boolean:
  string-contains(id, "-$")
end

fun is-decl-port(id :: Port) -> Boolean:
  string-contains(id, "-&")
end

fun is-var-port(id :: Port) -> Boolean:
  is-refn-port(id) or is-decl-port(id)
end

data Bind:
  | bind(refn, decls)
end

type Conj = List<R.Fact>

data Constraint:
  | constraint(left :: Conj, right :: Conj)
sharing:
  show(self):
    self.left.map(_.show()).join-str(" & ")
      + "   iff   "
      + self.right.map(_.show()).join-str(" & ")
  end
end

fun print-constraints(cs):
  print("[Constraints:")
  for each(c from cs):
    print("   " + c.show())
  end
  print("]")
end

fun print-facts(facts):
  print("[Facts:")
  for each(fact from facts):
    print("    " + fact.show())
  end
  print("]")
end


fun gen-constraints(lhs :: T.Term, rhs :: T.Term) -> List<Constraint>:
  holes = lhs.get-holes() # Assumption: LHS and RHS have same hole set
  ports = holes + [list: "!root"]
  
  var constraints = [list:]
  for map(p from ports):
    for map(q from ports):
      when p <> q:
        c = constraint(gen-conj(lhs, p, q), gen-conj(rhs, p, q))
        constraints := link(c, constraints)
      end
    end
  end
  constraints
end


fun gen-conj(t :: T.Term, a, b) -> Conj:
  shadow a =
    if a == "!root": [list:]
    else: t.get-path-to-hole(a).value
    end
  
  shadow b =
    if b == "!root": [list:]
    else: t.get-path-to-hole(b).value
    end
  
  fun gen(shadow t :: T.Term, shadow a, shadow b):
    cases(T.Term) t:
      | stx(con, _, _, ts) =>
        cases(List) a:
          | empty => cases(List) b:
              | empty =>
                # S-Self
                [list: R.fact(con, R.bot, R.top)]
              | link(i, shadow b) =>
                # SA-Child
                [list: R.fact(con, R.bot, R.child(i))]
                  + gen(ts.get(i), [list:], b)
            end
          | link(i, shadow a) => cases(List) b:
              | empty =>
                # SA-Parent
                [list: R.fact(con, R.child(i), R.top)]
                  + gen(ts.get(i), a, [list:])
              | link(j, shadow b) =>
                if i == j:
                  # S-Lift
                  gen(ts.get(i), a, b)
                else:
                  # SA-Sibling
                  [list: R.fact(con, R.child(i), R.child(j))]
                    + gen(ts.get(i), a, [list:])
                    + gen(ts.get(j), [list:], b)
                end
            end
        end
      | hole(_, _) =>
        if is-empty(a) and is-empty(b):
          # Assuming (bot <* top) for all terms t - follows from lexical scope
          [list:]
        else:
          raise("Generate conjunction: bad path to hole")
        end
      | else => raise("Generate conjunction: bad path")
    end
  end
  
  gen(t, a, b)
end


fun solve-constraints(arities :: D.MutableStringDict<Number>, rules :: R.RuleSet, cs :: List<Constraint>) -> R.RuleSet:
  
  fun solve-constraint(c, db):
    l-conj = c.left
    r-conj = c.right
    new-l-conj = for filter(fact from l-conj):
      not(db.member(fact))
    end
    new-r-conj = for filter(fact from r-conj):
      not(db.member(fact))
    end
    if is-empty(new-l-conj):
      print("Learned facts:")
      print-facts(new-r-conj)
      { constr: none, changed: true, db: new-r-conj + db }
    else if is-empty(new-r-conj):
      print("Learned facts:")
      print-facts(new-l-conj)
      { constr: none, changed: true, db: new-l-conj + db }
    else if (new-l-conj <> l-conj) or (new-r-conj <> r-conj):
      shadow c = constraint(new-l-conj, new-r-conj)
      { constr: some(c), changed: true, db: db }
    else:
      { constr: some(c), changed: false, db: db }
    end
  end
  
  fun iter(old-cs, new-cs, db, changed):
    cases(List) old-cs:
      | empty => { cs: new-cs, db: db, changed: changed }
      | link(c, shadow old-cs) =>
        ans = solve-constraint(c, db)
        shadow new-cs = cases(Option) ans.constr:
          | none        => new-cs
          | some(new-c) => link(new-c, new-cs)
        end
        iter(old-cs, new-cs, ans.db, changed or ans.changed)
    end
  end
  
  fun recur(shadow cs, db):
    ans = iter(cs, [list:], db, false)
    if ans.changed:
      recur(ans.cs, ans.db)
    else:
      print("Final constraints:")
      print-constraints(ans.cs)
      print("Final facts:")
      print-facts(ans.db)
      ans.db
    end
  end
  
  db = R.rules-to-facts(rules)
  facts = recur(cs, db)
  R.facts-to-rules(arities, facts)
end

fun resugar-scope(
    sugar :: List<Pair<T.Term, T.Term>>,
    arities :: D.MutableStringDict<Number>,
    rules :: R.RuleSet)
  -> R.RuleSet:
  
  cs = append-lists(
    for map(sugar-rule from sugar):
      gen-constraints(sugar-rule.left, sugar-rule.right)
    end)
  solve-constraints(arities, rules, cs)
end


fun compute-scope(rules :: R.RuleSet, t :: T.Term) -> P.Preorder:
  doc: "Compute the preorder over a term using the Declarative Scope Checking inference rules"
  edge = P.edge
  fun compute(shadow t :: T.Term):
    in = make-in-port(t)
    out = make-out-port(t)
    nodes-and-edges = cases(T.Term) t:
      | refn(_)    => {edges: [list:], nodes: [list: in, out]}
      | val(_, _)  => {edges: [list:], nodes: [list: in, out]}
      | hole(_, _) => {edges: [list:], nodes: [list: in, out]}
        # S-Decl
      | decl(_)    => {edges: [list: edge(out, in)], nodes: [list: in, out]}
      | stx(con, _, _, ts) =>
        child-scopes = map(compute, ts)
        var nodes = [list: in, out]
        var edges = [list:]
        for each(lt from rules.get-value-now(con).to-list()):
          new-edges = cases(R.Elem) lt.left:
            | bot =>
              cases(R.Elem) lt.right:
                  # S-Self
                | top => [list: edge(out, in)]
                  # SD-Child
                | child(i) => [list: edge(out, child-scopes.get(i).out)]
                | bot => raise("compute-scope: invalid rule")
              end
            | child(i) =>
              cases(R.Elem) lt.right:
                  # SD-Parent
                | top => [list: edge(child-scopes.get(i).in, in)]
                  # SD-Sibling
                | child(j) => [list: edge(
                      child-scopes.get(i).in,
                      child-scopes.get(j).out)]
                | bot => raise("compute-scope: invalid rule")
              end
            | top => raise("compute-scope: invalid rule")
          end
          edges := edges + new-edges
        end
        for each(scope from child-scopes):
          # S-Lift
          edges := edges + scope.edges
          nodes := nodes + scope.nodes
        end
        {edges: edges, nodes: nodes}
      | mac(_, _, _, _) => raise("compute-scope: unexpected desugaring context")
      | tag(_, _, _) => raise("compute-scope: unexpected tag")
    end
    {edges: nodes-and-edges.edges, nodes: nodes-and-edges.nodes, in: in, out: out}
  end
  # S-Refl1, S-Refl2, SD-Trans
  answer = compute(t)
  P.preorder(answer.nodes, answer.edges)
    .transitive-closure()
  #.reflexive-closure()
end

fun compute-var-scope(rules :: R.RuleSet, t :: T.Term) -> P.Preorder:
  order = compute-scope(rules, t)
  order.filter(lam(id):
      # Restrict the preorder to the terms' variables
      is-var-port(id)
    end)
end

fun compute-bindings(rules :: R.RuleSet, t :: T.Term) -> List<Bind>:
  # TODO: Compute conflicting declarations
  scope = compute-var-scope(rules, t)
  refns = scope.nodes.filter(is-refn-port)
  for map(refn from refns):
    decls = scope.greators(refn)
    shadow decls = for filter(decl from decls):
      lookup-port(t, refn).v.name == lookup-port(t, decl).v.name
    end
    shadow decls = scope.min(decls)
    
    shadow refn = lookup-port(t, refn)
    shadow decls = map(lookup-port(t, _), decls)
    bind(refn, decls)
  end
end

fun compute-bindings-incorrect(rules :: R.RuleSet, t :: T.Term) -> List<Bind>:
  scope = compute-scope(rules, t)
  toposorted = scope.toposort(make-in-port(t))
  shadow toposorted = for map(group from toposorted):
    for filter(id from group):
      is-var-port(id)
    end
  end
  shadow toposorted = for filter(group from toposorted):
    not(is-empty(group))
  end
  shadow scope = scope.filter(lam(id): is-var-port(id) end)
  
  fun is-decl-group(var-group):
    for all(id from var-group):
      string-contains(id, "&")
    end
  end
  fun is-refn-group(var-group):
    (var-group.length() == 1) and
    for all(id from var-group):
      string-contains(id, "$")
    end
  end
  fun env-shadow(env1, env2):
    env3 = list-to-list-set(
      for filter(id1 from env1.to-list()):
        not(for any(id2 from env2.to-list()):
            lookup-port(t, id1).v.name == lookup-port(t, id2).v.name
          end)
      end)
    env2.union(env3)
  end
  
  envs = [D.mutable-string-dict:]
  var bindings = [list:]
  
  for each(group from toposorted):
    if is-decl-group(group):
      env1 = for fold(env from [S.list-set:], id from scope.preds(group)):
        env.union(envs.get-value-now(id))
      end
      env2 = S.list-to-list-set(group)
      env = env-shadow(env1, env2)
      for each(id from group):
        envs.set-now(id, env)
      end
    else if is-refn-group(group):
      refn = lookup-port(t, group.get(0))
      env = for fold(env from [S.list-set:], id from scope.preds(group)):
        env.union(envs.get-value-now(id))
      end
      env-decls = for map(id from env.to-list()):
        lookup-port(t, id)
      end
      decls = for filter(decl from env-decls):
        decl.v.name == refn.v.name
      end
      bindings := link(bind(refn, decls), bindings)
    else:
      raise("Compute bindings: unexpected mixed variable group")
    end
  end
  
  bindings
end
