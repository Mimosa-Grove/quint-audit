module Ql008HelperAll {
  var a: int
  var b: int
  action init = all { a' = 0, b' = 0 }
  action setAll(v) = all { a' = v, b' = v }
  action register =
    nondet d = Set(0, 1).oneOf()
    setAll(d)
  action step = any { register }
}
