module Ql001Thin {
  var x: int
  def stateReading: int = x + 1
  pure def inc(v: int): int = v + 1
  action init = all { x' = 0 }
  action advance = all { x' = stateReading + inc(x) }
  action fallback = any { all { x' = inc(x) }, x' = x }
  action step = any { advance, fallback }
}
