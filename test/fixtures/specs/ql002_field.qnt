module Ql002Field {
  var r: { f: int }
  var role: str
  val fieldOk = r.f == 0
  val realString = role == "leader"
  action init = all { r' = { f: 0 }, role' = role }
  action step = any { all { r' = { f: r.f + 1 }, role' = role } }
}
