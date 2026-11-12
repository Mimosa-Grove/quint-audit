module Qp002Clean {
  var x: int
  pure def good(v: int): int = v + 1
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
