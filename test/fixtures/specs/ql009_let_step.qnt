module Ql009LetStep {
  var x: int
  action init = all { x' = 0 }
  action a = all { x' = x }
  action step = nondet w = oneOf(Set(1, 2)) { any { a } }
}
