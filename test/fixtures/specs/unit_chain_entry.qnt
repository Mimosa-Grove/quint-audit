// Fixture: runnable entry reaching the leaf through the middle module.
module UnitChainEntry {
  import UnitMid.* from "./unit_mid"
  var t: int
  action init = all { t' = 0 }
  action advance = all { t' = t + 1 }
  action step = any { advance }
}
