module FullInvariantPureVal {
  var x: int
  pure val voidP = true
  action init = all { x' = 0 }
  action advance = all { x' = 1 }
  action step = any { advance }
}
