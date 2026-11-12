module Qp001LiteralFalse {
  var x: int
  val contradiction = and { x > 0, not(x > 0) }
  val void = x == x
  val fine = x > 0 and x < 10
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
