module Ql008HelperPartial {
  var a: int
  var b: int
  action init = all { a' = 0, b' = 0 }
  action setA = all { a' = 1 }
  action wrapper =
    nondet d = Set(0, 1).oneOf()
    setA
  action step = any { wrapper }
}
