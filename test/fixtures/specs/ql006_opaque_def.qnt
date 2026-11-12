module Ql006OpaqueDef {
  const LIMIT: int
  var x: int
  def stateDef(v: int): int = v + x
  val b = stateDef(LIMIT)
  val a = b
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
