module Ql001ThinLeaf {
  var x: int
  action init = all { x' = 0 }
  action advance = x' = x + 1
  action step = any { advance }
}
