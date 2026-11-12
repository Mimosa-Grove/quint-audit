module FullViolation {
  var x: int
  pure def inc(v: int): int = v + 1
  val small = x >= 0 and x < 3
  action init = all { x' = 0 }
  action advance = all { x' = inc(x) }
  action step = any { advance }
}
