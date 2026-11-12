module FullWitnessInitOnly {
  var x: int
  val initOnly = x == 0
  action init = all { x' = 0 }
  action advance = all { x' = x + 1 }
  action step = any { advance }
}
