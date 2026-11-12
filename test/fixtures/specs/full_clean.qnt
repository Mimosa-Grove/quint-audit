module FullClean {
  var x: int
  pure def inc(v: int): int = v + 1
  val belowLimit = x >= 0 and x < 100
  action init = all { x' = 0 }
  action advance = all { x' = inc(x) }
  action step = any { advance }
}
