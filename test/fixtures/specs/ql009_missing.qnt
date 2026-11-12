module Ql009Missing {
  var x: int
  action init = all { x' = 0 }
  action a = all { x' = x }
}
