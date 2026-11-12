module Ql006ParamSubjects {
  var x: int
  val pv(v: int): bool = false
  temporal tp(v: int): bool = false
  val plain = x >= 0 and x < 100
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
