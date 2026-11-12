module Qp002ParamRenamed {
  var pl: int
  pure def f(p: int): int = p - 1
  action init = all { pl' = 0 }
  action step = any { all { pl' = f(pl) } }
}
