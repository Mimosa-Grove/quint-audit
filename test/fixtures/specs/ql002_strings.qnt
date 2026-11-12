module Ql002Strings {
  var role: str
  val isLeader = role == "leader"
  action init = all { role' = "follower" }
  action setLeader = all { role' = "leader" }
  action step = any { setLeader }
}
