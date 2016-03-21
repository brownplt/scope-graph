provide *

fun make-fresh():
  var next-id = 0
  {
    next: lam():
        next-id := next-id + 1
        next-id
      end,
    reset: lam():
        next-id := 0
      end
  }
end



check:
  f1 = make-fresh()
  f1.next() is 1
  f1.next() is 2
  f2 = make-fresh()
  f2.next() is 1
  f1.next() is 3
  f2.next() is 2
  f1.reset()
  f1.next() is 1
  f2.next() is 3
end