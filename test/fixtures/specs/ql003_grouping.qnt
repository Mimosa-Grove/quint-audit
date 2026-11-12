module Ql003Grouping {
  var a: int
  var b: int
  action init = all { a' = 0, b' = 0 }
  action both1 = all { a' = a + 1, b' = b + 1 }
  action both2 = all { a' = a + 2, b' = b + 2 }
  action step = any { both1, both2 }
}
