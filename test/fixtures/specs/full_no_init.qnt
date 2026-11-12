module FullNoInit {
  var x: int
  val inRange = x >= 0 and x < 100
  action advance = all { x' = x + 1 }
  action step = any { advance }
}
