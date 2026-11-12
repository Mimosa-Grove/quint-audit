module Ql006PureTautology {
  var x: int
  pure val pureValTaut = true
  pure def pureDefTaut = true
  pure def inc(v: int): int = v + 1
  action init = all { x' = 0 }
  action step = any { all { x' = inc(x) } }
}
