module Ql008Clean {
  var x: int
  var y: int
  action init = all { x' = 0, y' = 0 }
  action advance = all { x' = x + 1, y' = y }
  action step = any { advance }
}
