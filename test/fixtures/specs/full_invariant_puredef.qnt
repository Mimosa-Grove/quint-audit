module FullInvariantPureDef {
  var x: int
  pure def readsState = x > 0
  action init = all { x' = 0 }
  action advance = all { x' = 1 }
  action step = any { advance }
}
