module Ql006PureParamBound {
  var x: int
  pure def used(v: int): bool = v > 0
  pure def unused(v: int): bool = true
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
