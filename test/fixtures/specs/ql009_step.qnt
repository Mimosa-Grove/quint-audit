module Ql009Step {
  var x: int
  action init = all { x' = 0 }
  action a = all { x' = x }
  action b = all { x' = x }
  action step = any { a }
}
