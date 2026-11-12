module Qp002ParamShadow {
  var pl: int
  pure def f(pl: int): int = pl - 1
  action init = all { pl' = 0 }
  action step = any { all { pl' = f(pl) } }
}
