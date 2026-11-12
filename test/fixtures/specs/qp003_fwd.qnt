module fwd {
  var x: int

  val usesLater = later + 1

  val later = x + 2

  action init = all {
    x' = 0,
  }

  action step = all {
    x' = x + 1,
  }

  val inv = usesLater >= 0
}
