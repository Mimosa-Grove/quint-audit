module Qp002PureDef {
  var x: int
  pure def bad: int = x + 1
  pure def good(v: int): int = v + 1
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
