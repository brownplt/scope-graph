provide *
provide-types *

data Pair:
  | pair(left, right)
end

fun append-lists(lsts):
  cases(List) lsts:
    | empty => empty
    | link(lst, shadow lsts) =>
      lst + append-lists(lsts)
  end
end

fun loop(func):
  doc: "Repeatedly run func() while it returns true."
  when func():
    loop(func)
  end
end

fun each-while1(func, lst):
  doc: "Run func(elem) for elem from list as long as it returns true."
  if is-empty(lst):
    true
  else if func(lst.first):
    each-while1(func, lst.rest)
  else:
    false
  end
end

fun each-while2(func, list1, list2):
  doc: "Run func(elem1, elem2) for elems from list1 and list2 as long as it returns true."
  fun recur(shadow list1, shadow list2):
    if is-empty(list1):
      true
    else if func(list1.first, list2.first):
      recur(list1.rest, list2.rest)
    else:
      false
    end
  end
  if list1.length() == list2.length():
    recur(list1, list2)
  else:
    false
  end
end

fun until-some(func, lst):
  doc: "Run func(elem) for elem from list until it returns a some(_)."
  cases(List) lst:
    | empty => none
    | link(first, rest) =>
      cases(Option) func(first):
        | none => until-some(func, rest)
        | some(answer) => some(answer)
      end
  end
end

fun map-option(func, lst):
  doc: "Run func(elem) for elem from list. Return the list of results, else none if any fails."
  cases(List) lst:
    | empty => some(empty)
    | link(first, rest) =>
      cases(Option) func(first):
        | none => none
        | some(shadow first) =>
          cases(Option) map-option(func, rest):
            | none => none
            | some(shadow rest) => some(link(first, rest))
          end
      end
  end
end

fun try-option(func, opt):
  cases(Option) opt:
    | none    => none
    | some(x) => func(x)
  end
end

fun string-starts-with(str, prefix):
  if string-length(str) < string-length(prefix):
    false
  else:
    string-substring(str, 0, string-length(prefix)) == prefix
  end
end

fun string-tail(str):
  when string-length(str) == 0:
    raise("string-tail: Attempted to take the tail of an empty string")
  end
  string-substring(str, 1, string-length(str))
end

upper = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

# Currently unused
fun is-capital(str):
  if string-length(str) == 0:
    false
  else:
    string-contains(upper, string-char-at(str, 0))
  end
end

check:
  for each-while1(x from [list: 1, 1, 1]):
    x == 1
  end is true
  
  for each-while1(x from [list: 1, 2, 1]):
    x == 1
  end is false
  
  for each-while2(x from [list: 1], y from [list: 2, 3]):
    true
  end is false
  
  for each-while2(x from [list: 1, 2], y from [list: 1, 2]):
    x == y
  end is true
  
  for each-while2(x from [list: 1, 2], y from [list: 1, 3]):
    x == y
  end is false
  
  for until-some(x from [list: none, some(1), some(2), none]):
    x
  end is some(1)
  
  for until-some(x from [list:]):
    x
  end is none
  
  for map-option(x from [list: 1, 2]):
    some(x + 1)
  end is some([list: 2, 3])
  
  for map-option(x from [list: 1, 2]):
    if x == 2: none
    else: some(x + 1)
    end
  end is none
  
  for map-option(x from [list: 1, 2]):
    none
  end is none
  
  string-starts-with("abc", "ab") is true
  string-starts-with("abc", "abcd") is false
  string-starts-with("abc", "") is true
  string-starts-with("abc", "aa") is false
  
  is-capital("abc") is false
  is-capital("Abc") is true
  is-capital("") is false
  is-capital("123") is false
  
  string-tail("") raises "tail"
  string-tail("a") is ""
  string-tail("Tall") is "all"
end