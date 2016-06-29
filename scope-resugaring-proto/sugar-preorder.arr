provide {edge: edge, preorder: preorder} end
provide-types *

import string-dict as D
import sets as S
import shuffle, all from lists

import make-fresh from my-gdrive("sugar/fresh.arr")
include my-gdrive("sugar/util.arr")

fresh = make-fresh()


fun toposort(root, next):
  doc: ```Toposort a directed graph (cycles are allowed).
       Nodes must be represented as strings.
       Root is the start node, and next(node) gives a list of
       all nodes node' such that there is an edge (node, node').
       ```
  # TODO: Remove assumption that everything is reachable from root
  
  # An ALGORITHM follows:
  fresh.reset()
  assignment = [D.mutable-string-dict:]
  inverse-assignment = [D.mutable-string-dict:]
  
  fun assign-fresh-id(node):
    id = fresh.next()
    when assignment.has-key-now(node):
      inverse-assignment.remove-now(tostring(assignment.get-value-now(node)))
    end
    inverse-assignment.set-now(tostring(id), [list: node])
    assignment.set-now(node, id)
  end
  
  fun merge(ids, to-id):
    # It's a cycle! Kill it!
    nodes = for fold(nodes from [list:], id from ids):
      nodes + inverse-assignment.get-value-now(tostring(id))
    end
    for each(node from nodes):
      assignment.set-now(node, to-id)
    end
    for each(id from ids):
      inverse-assignment.remove-now(tostring(id))
    end
    shadow nodes = nodes + inverse-assignment.get-value-now(tostring(to-id))
    inverse-assignment.set-now(tostring(to-id), nodes)
  end
  
  fun recur(stack, node):
    if stack.member(node): # It's a cycle.
      id = assignment.get-value-now(node)
      # Find all the ids involved in the cycle
      ids = stack
        .filter(lam(n): assignment.get-value-now(n) > id end)
        .map(lam(n): assignment.get-value-now(n) end)
      # Kill the cycle.
      merge(ids, id)
    else:
      assign-fresh-id(node)
      for each(child from next(node).to-list()):
        recur(link(node, stack), child)
      end
    end
  end
  recur([list:], root)
  
  inverse-assignment
    .keys-now()
    .to-list()
    .map(string-to-number)
    .map(_.value)
    .sort()
    .map(lam(id): inverse-assignment.get-value-now(tostring(id)) end)
end


data Edge:
  | edge(a, b)
end

# Inefficient for the moment
data Preorder:
  | preorder(nodes, edges)
sharing:
  
  less-than(self, a, b):
    self.edges.member(edge(a, b))
  end,
  
  to-list(self):
    self.edges
  end,
  
  reflexive-closure(self):
    edges = self.edges
    vertices = for fold(s from [S.set:], e from edges):
      s.add(e.a).add(e.b)
    end
    var new-edges = [list:]
    for each(v from vertices.to-list()):
      when not(edges.member(edge(v, v))):
        new-edges := link(edge(v, v), new-edges)
      end
    end
    preorder(self.nodes, edges + new-edges)
  end,
  
  transitive-closure(self):
    edges = self.edges
    var new-edges = [list:]
    for each(e from edges):
      for each(f from edges):
        when e.b == f.a:
          g = edge(e.a, f.b)
          when not(edges.member(g)) and not(new-edges.member(g)):
            new-edges := link(g, new-edges)
          end
        end
      end
    end
    if is-empty(new-edges):
      self
    else:
      preorder(self.nodes, edges + new-edges).transitive-closure()
    end
  end,
  
  min(self, nodes):
    for filter(n from nodes):
      for all(m from nodes):
        (n == m) or not(self.less-than(m, n))
      end
    end
  end,
  
  greators(self, node):
    for filter(n from self.nodes):
      self.less-than(node, n)
    end
  end,
  
  preds(self, nodes):
    bigger-nodes = for filter(n from self.nodes):
      for any(m from nodes): self.less-than(m, n) end
      and not(nodes.member(n))
    end
    self.min(bigger-nodes)
  end,
  
  filter(self, pred):
    nodes = for filter(n from self.nodes):
      pred(n)
    end
    edges = for filter(e from self.edges):
      pred(e.a) and pred(e.b)
    end
    preorder(nodes, edges)
  end,
  
  toposort(self, root):
    fun next(node):
      edges = self.edges.filter(lam(e): e.b == node end)
      S.list-to-list-set(edges.map(_.a))
    end
    toposort(root, next)
  end
end


# Test Cases

check "Transitive Relfexive Closure":
  p = preorder(
    [list: "a", "b", "c", "d"],
    [list:
      edge("a", "b"), edge("c", "a"), edge("b", "d"), edge("c", "d")
    ])
  p-trans = p.transitive-closure()
  
  p-trans.less-than("a", "a") is false
  p-trans.less-than("a", "b") is true
  p-trans.less-than("a", "c") is false
  p-trans.less-than("a", "d") is true
  
  p-trans.less-than("b", "a") is false
  p-trans.less-than("b", "b") is false
  p-trans.less-than("b", "c") is false
  p-trans.less-than("b", "d") is true
  
  p-trans.less-than("c", "a") is true
  p-trans.less-than("c", "b") is true
  p-trans.less-than("c", "c") is false
  p-trans.less-than("c", "d") is true
  
  p-trans.less-than("d", "a") is false
  p-trans.less-than("d", "b") is false
  p-trans.less-than("d", "c") is false
  p-trans.less-than("d", "d") is false
  
  p-trans.edges.length() is 6
  
  p-refl = p-trans.reflexive-closure()
  
  p-refl.less-than("a", "a") is true
  p-refl.less-than("a", "b") is true
  p-refl.less-than("a", "c") is false
  p-refl.less-than("a", "d") is true
  
  p-refl.less-than("b", "a") is false
  p-refl.less-than("b", "b") is true
  p-refl.less-than("b", "c") is false
  p-refl.less-than("b", "d") is true
  
  p-refl.less-than("c", "a") is true
  p-refl.less-than("c", "b") is true
  p-refl.less-than("c", "c") is true
  p-refl.less-than("c", "d") is true
  
  p-refl.less-than("d", "a") is false
  p-refl.less-than("d", "b") is false
  p-refl.less-than("d", "c") is false
  p-refl.less-than("d", "d") is true
  
  p-refl.edges.length() is 10
  
  r = p-refl.filter(lam(x): [list: "a", "c", "d"].member(x) end)
  
  r.less-than("a", "a") is true
  r.less-than("a", "c") is false
  r.less-than("a", "d") is true
  
  r.less-than("c", "a") is true
  r.less-than("c", "c") is true
  r.less-than("c", "d") is true
  
  r.less-than("d", "a") is false
  r.less-than("d", "c") is false
  r.less-than("d", "d") is true
  
  r.edges.length() is 6
end



check "Toposort":
  nodes = string-explode("abcdefgh")
  edges = [list:
    edge("g", "h"),
    edge("g", "c"),
    edge("c", "f"),
    edge("b", "f"),
    edge("e", "b"),
    edge("d", "e"),
    edge("e", "d"),
    edge("h", "h"),
    edge("h", "c"),
    edge("c", "a"),
    edge("b", "a"),
    edge("f", "e")
  ]
  
  order = preorder(nodes, edges)
  groups = order.toposort("a")
  
  check:
    for map(group from groups):
      group.sort().join-str("")
    end
      is [list: "a", "bdef", "c", "h", "g"]
  end
end