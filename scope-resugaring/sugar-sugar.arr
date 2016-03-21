provide *
provide-types *

import string-dict as D
import srcloc as Srcloc

import my-gdrive("sugar/term.arr") as T
import make-fresh from my-gdrive("sugar/fresh.arr")
import my-gdrive("sugar/subs.arr") as S
include my-gdrive("sugar/util.arr")

no-loc = Srcloc.builtin("dummy location")

fresh = make-fresh()


data Rule:
  | mk-rule(lhs :: T.Term, rhs :: T.Term)
end

fun add-rule(rules, lhs, rhs):
  rule = mk-rule(T.parse-term(lhs).strip(), T.parse-term(rhs).strip())
  con = rule.lhs.con # TODO: safety
  cases(Option) rules.get-now(con):
    | none      => rules.set-now(con, [list: rule])
    | some(lst) => rules.set-now(con, lst + [list: rule]) # TODO: efficiency
  end
end

type Sugar = D.MutableStringDict<List<Rule>> # Map from macro name to rule set

fun desugar-prog(sugar :: Sugar, t :: T.Term) -> T.Term:
  desugar(sugar, T.mac("prog", 0, t.loc, [list: t]))
end

fun desugar(sugar, t):
  cases(T.Term) t:
    | mac(con, _, _, _) =>
      cases(Option) sugar.get-now(con):
        | some(rules) =>
          cases(Option) desugar-macro(rules, t):
            | some(shadow t) => desugar(sugar, t)
            | none => raise("Desugar: no rule found for the macro call '" + t.show() + "'")
          end
        | none => raise("Desugar: no rule found for the sugar '" + con + "'")
      end
    | stx(con, id, l, ts) =>
      T.stx(con, id, l, map(desugar(sugar, _), ts))
    | tag(lhs, rhs, shadow t) =>
      T.tag(lhs, rhs, desugar(sugar, t))
    | else => t
  end
end

fun desugar-macro(rules :: List<Rule>, t :: T.Term) -> Option<T.Term>:
  for until-some(rule from rules):
    for try-option(subs from S._match(t, rule.lhs)):
      lhs = S.get-shell(t, rule.lhs)
      rhs = rule.rhs.freshen()
      ans = S.substitute(subs, rhs)
      some(T.tag(lhs, rhs, ans))
    end
  end
end

