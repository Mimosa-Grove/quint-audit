module Qp001Clean {
  var x: int
  val fine = x > 0 and x < 10
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
