module Ql008HelperCycle {
  var a: int
  var b: int
  action init = all { a' = 0, b' = 0 }
  action ping = all { a' = 1 }
  action pong = all { b' = 1 }
  action step = any { ping, pong }
}
