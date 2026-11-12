module Ql006ParamSeed {
  var limit: int
  val shadowed(limit: int): bool = limit == 5
  action init = all { limit' = 0 }
  action step = any { all { limit' = limit } }
}
