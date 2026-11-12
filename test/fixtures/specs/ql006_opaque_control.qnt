module Ql006OpaqueControl {
  const LIMIT: int
  var x: int
  def stateDef(v: int): int = v + x
  val c: bool = stateDef(LIMIT) > 0
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
