module Ql002FieldClean {
  var r: { f: int }
  val fieldOk = r.f == 0
  action init = all { r' = { f: 0 } }
  action step = any { all { r' = { f: r.f + 1 } } }
}
