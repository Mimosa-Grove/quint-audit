module Ql006Invariants {
  const LIMIT: int
  var x: int
  val literal = true
  val premise = LIMIT > 2
  val real = x > 0 and x < 100
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
