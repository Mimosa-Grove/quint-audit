module Ql008HelperChain {
  var a: int
  var b: int
  action init = all { a' = 0, b' = 0 }
  action leaf = all { a' = 1, b' = 1 }
  action middle = leaf
  action chain = middle
  action step = any { chain }
}
