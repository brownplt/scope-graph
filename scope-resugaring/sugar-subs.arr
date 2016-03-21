provide {
  substitute: substitute,
  _match: _match,
  get-shell: get-shell
} end
provide-types {
  Subs:: Subs
}

import string-dict as D
import srcloc as S

import my-gdrive("sugar/term.arr") as T
include my-gdrive("sugar/util.arr")


type Subs = D.MutableStringDict<T.Term>


fun substitute(subs :: Subs, ctx :: T.Term) -> T.Term:
  doc: "Replace this context's holes with concrete terms. Each hole must be bound in subs."
  cases(T.Term) ctx:
    | hole(_, h) => subs.get-value-now(h)
    | decl(_) => ctx
    | refn(_) => ctx
    | val(_)  => ctx
    | stx(con, id, l, ctxs) =>
      T.stx(con, id, l, map(substitute(subs, _), ctxs))
    | mac(con, id, l, ctxs) =>
      T.mac(con, id, l, map(substitute(subs, _), ctxs))
    | tag(_, _, _) =>
      raise("Substitute: cannot substitute into tagged term.")
  end
end

fun _match(t :: T.Term, ctx :: T.Term) -> Option<Subs>:
  # TODO: test for id==0 correct?
  doc: "Match a term against a context to find a substitution s such that subs(s, ctx) = t"
  
  subs = [D.mutable-string-dict:]
  
  fun matchRec(shadow t, shadow ctx):
    cases(T.Term) ctx:
      | hole(_, h)  =>
        subs.set-now(h, t)
        true
      | decl(v)  => T.is-decl(t) and (t.v == v)
      | refn(v)  => T.is-refn(t) and (t.v == v)
      | val(id, val) => T.is-val(t) and (t.val == val)
        and ((id == 0) or (t.id == id))
      | stx(con, id, l, ctxs) =>
        if T.is-stx(t) and (t.con == con) and ((id == 0) or (t.id == id)):
          for each-while2(shadow t from t.subterms, shadow ctx from ctxs):
            matchRec(t, ctx)
          end
        else:
          false
        end
      | mac(con, id, l, ctxs) =>
        if T.is-mac(t) and (t.con == con) and ((id == 0) or (t.id == id)):
          for each-while2(shadow t from t.subterms, shadow ctx from ctxs):
            matchRec(t, ctx)
          end
        else:
          false
        end
    end
  end
  
  if matchRec(t, ctx):
    some(subs)
  else:
    none
  end
end

fun get-shell(t :: T.Term, ctx :: T.Term) -> T.Term:
  doc: "Get the part of a term that overlaps with a context. Requires that _match(t, ctx) succeeds."
  cases(T.Term) ctx:
    | hole(id, h) => ctx
    | decl(_) => t
    | refn(_) => t
    | val(_)  => t
    | stx(_, _, _, ctxs) =>
      T.stx(t.con, t.id, t.loc, map2(get-shell, t.subterms, ctxs))
    | mac(_, _, _, ctxs) =>
      T.mac(t.con, t.id, t.loc, map2(get-shell, t.subterms, ctxs))
    | tag(_, _, _) =>
      raise("GetShell: cannot match against tagged context")
  end
end



check:
  no-loc = S.builtin("dummy location")
  fun lam-node(param, body):
    T.mac("lam", 0, no-loc, [list: param, body])
  end
  fun app-node(func, arg):
    T.stx("app", 0, no-loc, [list: func, arg])
  end
  fun let-node(param, val, body):
    T.stx("let", 0, no-loc, [list: param, val, body])
  end
  
  lhs = let-node(T.hole(0, "a"), T.hole(0, "b"), T.hole(0, "c"))
  rhs = app-node(lam-node(T.hole(0, "a"), T.hole(0, "c")), T.hole(0, "b"))
  fun expand(t):
    for try-option(subs from _match(t, lhs)):
      some(substitute(subs, rhs))
    end
  end
  fun unexpand(t):
    for try-option(subs from _match(t, rhs)):
      some(substitute(subs, lhs))
    end
  end
  
  x = T.new-var("x")
  y = T.new-var("y")
  t1 = let-node(T.decl(x), lam-node(T.decl(y), T.refn(y)), T.refn(x))
  t2 = app-node(lam-node(T.decl(x), T.refn(x)), lam-node(T.decl(y), T.refn(y)))
  
  expand(t1)   is some(t2)
  unexpand(t2) is some(t1)
  unexpand(t1) is none
end