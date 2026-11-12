module FullInitFalse {
  var x: int
  val inRange = x >= 0 and x < 100
  action init = all { x' = 0, false }
  action advance = all { x' = x }
  action step = any { advance }
}
