module FullInvariantNonBoolean {
  var x: int
  val nonBoolean = x
  action init = all { x' = 0 }
  action advance = all { x' = 1 }
  action step = any { advance }
}
