module Ql006PureChain {
  var x: int
  pure val pv = x > 0
  val built = pv
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
