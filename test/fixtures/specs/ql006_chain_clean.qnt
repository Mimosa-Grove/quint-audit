module Ql006ChainClean {
  const LIMIT: int
  var x: int
  val later = x + 2
  val usesLater = later + 1
  val bounded = usesLater + 1 > later
  action init = all { x' = 0 }
  action step = any { all { x' = x + 1 } }
}
