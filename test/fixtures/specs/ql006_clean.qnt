module Ql006Clean {
  const LIMIT: int
  var x: int
  val real = x > 0 and x < 100
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
