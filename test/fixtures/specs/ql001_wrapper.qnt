module Ql001Wrapper {
  var x: int
  action init = all { x' = 0 }
  action registerBackend(v) = all { x' = v }
  action register =
    nondet b = Set(0, 1).oneOf()
    registerBackend(b)
  action step = any { register }
}
