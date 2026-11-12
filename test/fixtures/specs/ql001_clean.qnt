module Ql001Clean {
  var x: int
  pure def inc(v: int): int = v + 1
  action init = all { x' = 0 }
  action advance = all { x >= 0, x' = inc(x) }
  action step = any { advance }
}
