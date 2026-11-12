module Ql006BoolTautology {
  var x: int
  val t: bool = true
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
