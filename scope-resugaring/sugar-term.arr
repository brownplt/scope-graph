provide *
provide-types *

import s-exp as S
import srcloc as Srcloc
import valueskeleton as VS

include my-gdrive("sugar/util.arr")
import make-fresh from my-gdrive("sugar/fresh.arr")

fresh = make-fresh()
fresh.next()
no-loc = Srcloc.builtin("dummy location")


type Id = Number
type Name = String
type Path = List<Number>

fun new-var(name :: Name):
  mk-var(name, fresh.next())
end

data Var:
  | mk-var(name :: Name, id :: Id)
sharing:
  show(self):
    self.name
  end,
  strip(self):
    mk-var(self.name, 0)
  end,
  freshen(self):
    mk-var(self.name, fresh.next())
  end
end

data Term:
  | decl(v :: Var)
  | refn(v :: Var)
  | val(id :: Id, val :: Any)
  | stx(con :: String, id :: Id, loc :: Srcloc.Srcloc, subterms :: List<Term>)
  | mac(con :: String, id :: Id, loc :: Srcloc.Srcloc, subterms :: List<Term>)
  | hole(id :: Id, name :: Name)
  | tag(lhs :: Term, rhs :: Term, term :: Term)
sharing:
  show-debug(self, show-ids):
    recur = lam(t): t.show-debug(show-ids) end
    str = cases(Term) self:
      | decl(x)     => "&" + x.name
      | refn(x)     => "$" + x.name
      | val(_, v)   => torepr(v)
      | stx(con, _, _, ts) => "(" + link(con, map(recur, ts)).join-str(" ") + ")"
      | mac(con, _, _, ts) => "(!" + link(con, map(recur, ts)).join-str(" ") + ")"
      | hole(_, name)      => name
      | tag(lhs, rhs, t)   => "{" + recur(lhs) + " => " + recur(rhs) + "}" + recur(t)
    end
    if show-ids and not(is-tag(self)):
      self.get-id() + ":" + str
    else:
      str
    end
  end,
  show(self):
    self.show-debug(false)
    cases(Term) self:
      | decl(x)     => "&" + x.name
      | refn(x)     => "$" + x.name
      | val(_, v)   => torepr(v)
      | stx(con, _, _, ts) => "(" + link(con, map(_.show(), ts)).join-str(" ") + ")"
      | mac(con, _, _, ts) => "(!" + link(con, map(_.show(), ts)).join-str(" ") + ")"
      | hole(_, name)      => name
      | tag(lhs, rhs, t)   => "{" + lhs.show() + " => " + rhs.show() + "}" + t.show()
    end
  end,
  _output(self):
    VS.vs-value(self.show())
  end,
  get-id(self) -> String:
    doc: "A unique id for every term"
    cases(Term) self:
      | stx(_, id, _, _) => tostring(id)
      | mac(_, id, _, _) => tostring(id)
      | decl(v)          => "&" + tostring(v.id)
      | refn(v)          => "$" + tostring(v.id)
      | val(id, _)       => tostring(id)
      | hole(_, name)    => "@" + name
      | tag(_, _, _)     => raise("Term.id: unexpected tag")
    end
  end,
  lookup(self, id :: String):
    doc: "Find the subterm with a given id"
    fun recur(t):
      if t.get-id() == id:
        some(t)
      else:
        cases(Term) t:
          | stx(_, _, _, ts) => until-some(recur, ts)
          | else => none
        end
      end
    end
    cases(Option) recur(self):
      | some(shadow id) => id
      | none => raise("Term.lookup - id not found: " + id)
    end
  end,
  strip(self):
    cases(Term) self:
      | stx(con, id, loc, ts) => stx(con, 0, loc, map(_.strip(), ts))
      | mac(con, id, loc, ts) => mac(con, 0, loc, map(_.strip(), ts))
      | decl(v)       => decl(v.strip())
      | refn(v)       => refn(v.strip())
      | val(_, v)     => val(0, v)
      | hole(_, name) => hole(0, name)
      | tag(_, _, t)  => t.strip()
    end
  end,
  freshen(self):
    cases(Term) self:
      | stx(con, _, loc, ts) => stx(con, fresh.next(), loc, map(_.freshen(), ts))
      | mac(con, _, loc, ts) => mac(con, fresh.next(), loc, map(_.freshen(), ts))
      | decl(v)        => decl(v.freshen())
      | refn(v)        => refn(v.freshen())
      | val(_, v)      => val(fresh.next(), v)
      | hole(_, name)  => hole(fresh.next(), name)
      | tag(_, _, _)   => raise("Term.freshen: cannot freshen tagged term")
    end
  end,
  get(self, i):
    cases(Term) self:
      | stx(_, _, _, ts) => ts.get(i)
      | else => raise("Term.get: subterm not found")
    end
  end,
  get-holes(self):
    cases(Term) self:
      | stx(_, _, _, ts) => append-lists(map(_.get-holes(), ts))
      | mac(_, _, _, ts) => append-lists(map(_.get-holes(), ts))
      | decl(v)          => [list:]
      | refn(v)          => [list:]
      | val(_, v)        => [list:]
      | hole(_, name)    => [list: name]
      | tag(_, _, t)     => raise("Term.get-holes: cannot search tagged term")
    end
  end,
  get-path-to-hole(self, name) -> Option<Path>:
    doc: "Find the path from the root to a hole."
    fun get-path-rec(ts, i):
      cases(List) ts:
        | empty => none
        | link(t, shadow ts) =>
          cases(Option) t.get-path-to-hole(name):
            | none => get-path-rec(ts, i + 1)
            | some(path) => some(link(i, path))
          end
      end
    end
    if is-hole(self) and (self.name == name):
      some([list:])
    else:
      cases(Term) self:
        | stx(_, _, _, ts) => get-path-rec(ts, 0)
        | mac(_, _, _, ts) => get-path-rec(ts, 0)
        | else => none
      end
    end
  end
end


fun parse-term(text):
  fun parse-expr(sexp):
    cases(S.S-Exp) sexp:
      | s-num(num)   => val(fresh.next(), num)
      | s-str(str)   => val(fresh.next(), str)
      | s-sym(sym)   =>
        if string-starts-with(sym, "&"):
          decl(new-var(string-tail(sym)))
        else if string-starts-with(sym, "$"):
          refn(new-var(string-tail(sym)))
        else:
          hole(fresh.next(), sym)
        end
      | s-list(lst) =>
        cases(List) lst:
          | link(head, tail) =>
            cases(S.S-Exp) head:
              | s-sym(sym) =>
                subterms = map(parse-expr, tail)
                if string-starts-with(sym, "!"):
                  shadow sym = string-substring(sym, 1, string-length(sym))
                  mac(sym, fresh.next(), no-loc, subterms)
                else:
                  stx(sym, fresh.next(), no-loc, subterms)
                end
              | else => raise("Parse: unexpected constructor: " + tostring(head))
            end
        end
      | empty => raise("Parse: unexpected empty node: ()")
    end
  end
  parse-expr(S.read-s-exp(text))
end


check "Variable":
  fresh.reset()
  
  x = new-var("x")
  x2 = new-var("x")
  x.strip() is x2.strip()
  x3 = x.freshen()
  x4 = x2.freshen()
  x.strip() is x2.strip()
  x is-not x3
  x2 is-not x3
  x is-not x4
  x2 is-not x4
  x3 is-not x4
  x2.strip() is x4.strip()
  
  y = new-var("y")
  x.strip() is-not y.strip()
end

check "Term":
  text = "(!Thunk (Lambda &x $y) \"ok\" A)"
  t = mac("Thunk", 0, no-loc, [list:
      stx("Lambda", 0, no-loc, [list:
          decl(new-var("x")), refn(new-var("y"))]),
      val(0, 'ok'),
      hole(0, "A")])
  t.show() is text
  tostring(t) is text
  parse-term(text).strip() is t.strip()
end