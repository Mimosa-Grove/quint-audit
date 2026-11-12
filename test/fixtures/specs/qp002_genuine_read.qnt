module Qp002GenuineRead {
  var pl: int
  pure def f(x: int): int = x + pl
  action init = all { pl' = 0 }
  action step = any { all { pl' = f(pl) } }
}
