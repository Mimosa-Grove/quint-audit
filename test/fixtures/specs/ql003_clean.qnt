module Ql003Clean {
  var a: int
  var b: int
  action init = all { a' = 0, b' = 0 }
  action first = all { a' = a + 1, b' = b }
  action second = all { a' = a, b' = b + 1 }
  action step = any { first, second }
}
