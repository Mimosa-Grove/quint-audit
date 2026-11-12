module Ql008Stutter {
  var a: int
  var b: int
  action init = all { a' = 0, b' = 0 }
  action advance = all { a' = a + 1 }
  action step = any { advance }
}
