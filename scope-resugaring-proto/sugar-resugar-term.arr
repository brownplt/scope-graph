import string-dict as D

import my-gdrive("sugar/term.arr") as T
import my-gdrive("sugar/subs.arr") as S
import my-gdrive("sugar/sugar.arr") as Sugar
include my-gdrive("sugar/util.arr")



fun resugar-prog(t :: T.Term) -> Option<T.Term>:
  cases(Option) resugar-term(t):
    | none => none
    | some(shadow t) => some(t.subterms.get(0))
  end
end

fun resugar-term(t):
  ans = cases(T.Term) t:
    | tag(lhs, rhs, shadow t) =>
      for try-option(shadow t from resugar-term(t)):
        for try-option(subs from S._match(t, rhs)):
          if resugar-term-subs(subs):
            some(S.substitute(subs, lhs))
          else:
            none
          end
        end
      end
    | stx(con, l, id, ts) =>
      shadow ts = for map-option(shadow t from ts):
        resugar-term(t)
      end
      for try-option(shadow ts from ts):
        some(T.stx(con, l, id, ts))
      end
    | mac(_, _, _, _)     => none
    | hole(_, _)          => raise("Resugar term: unexpected hole")
    | else                => some(t)
  end
  cases(Option) ans:
    | none => none
    | some(shadow t) =>
      if T.is-Term(t):
        some(t)
      else:
        none
      end
  end
end

fun resugar-term-subs(subs :: S.Subs) -> Boolean:
  for each-while1(key from subs.keys-now().to-list()):
    cases(Option) resugar-term(subs.get-value-now(key)):
      | none    => false
      | some(t) =>
        subs.set-now(key, t)
        true
    end
  end
end



check:
  rules = [D.mutable-string-dict:]
  fun rule(lhs, rhs):
    Sugar.add-rule(rules, lhs, rhs)
  end
  rule(
    "(!prog A)",
    "(!expr A)")
  rule(
    "(!expr (let A B C))",
    "(apply (lambda (!patt A) (!expr C)) (!expr B))")
  rule(
    "(!expr (lambda X B))",
    "(lambda (!patt X) (!expr B))")
  rule(
    "(!expr A)",
    "A")
  rule(
    "(!patt A)",
    "A")
  
  fun test(t-in, t-out):
    shadow t-in = T.parse-term(t-in).strip()
    shadow t-out = T.parse-term(t-out).strip()
    t-desugared = Sugar.desugar-prog(rules, t-in)
    t-desugared.strip() is t-out
    resugar-prog(t-desugared) is some(t-in)
  end

  test("(let @x 1 $x)", "(apply (lambda @x $x) 1)")
  test(
    "(let @x 1 (lambda @x (let @y 2 $x)))",
    "(apply (lambda @x (lambda @x (apply (lambda @y $x) 2))) 1)")
end