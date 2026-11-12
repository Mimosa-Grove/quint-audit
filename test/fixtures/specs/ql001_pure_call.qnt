module Ql001PureCall {
  var x: int
  pure def setX(): int = x' = 1
  action init = all { x' = 0 }
  action wrapper = setX()
  action step = any { wrapper }
}
