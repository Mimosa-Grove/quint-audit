module BadNonAscii {
  // café
  var x: int
  action init = all { x' = 0 }
  action step = any { all { x' = x } }
}
