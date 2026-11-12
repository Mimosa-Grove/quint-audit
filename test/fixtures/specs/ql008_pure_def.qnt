module Ql008PureDef {
  var a: int
  var b: int
  pure def setA(): int = a' = 1
  action init = all { a' = 0, b' = 0 }
  action wrapper = setA()
  action step = any { wrapper }
}
