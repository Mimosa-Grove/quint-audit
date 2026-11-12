module Ql009Orphan {
  var x: int
  action init = all { x' = 0 }
  action a = all { x' = x }
  action b = all { x' = 1 }
  action step = any { a }
}
