module Qp002LetShadow {
  var pl: int
  pure def f(x: int): int = val pl = 1; x + pl
  action init = all { pl' = 0 }
  action step = any { all { pl' = f(pl) } }
}
