module Ql009HelperReach {
  var x: int
  action init = all { x' = 0 }
  action cleanup = all { x' = 1 }
  action housekeeping = cleanup()
  action a = all { x' = x }
  action step = any { a, housekeeping }
}
