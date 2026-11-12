module Ql009Cycle {
  var x: int
  action init = all { x' = 0 }
  action a = all { x' = 1 }
  action b = all { x' = 2 }
  action step = any { a }
}
