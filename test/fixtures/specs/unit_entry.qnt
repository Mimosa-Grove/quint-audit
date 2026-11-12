// Fixture: a runnable entry that imports the stepless helper.
module UnitEntry {
  import UnitHelper.* from "./unit_helper"
  var t: int
  action init = all { t' = 0 }
  action advance = all { t' = t + 1 }
  action step = any { advance }
}
