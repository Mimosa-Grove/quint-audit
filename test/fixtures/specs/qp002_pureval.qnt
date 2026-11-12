module Qp002PureVal {
  var x: int
  pure val bad = x + 1
  pure val good = 2 + 1
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
