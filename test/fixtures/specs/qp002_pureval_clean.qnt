module Qp002PureValClean {
  var x: int
  pure val good = 2 + 1
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
