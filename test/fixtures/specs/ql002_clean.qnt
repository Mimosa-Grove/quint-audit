module Ql002Clean {
  type Role = | Leader | Follower
  var role: Role
  pure def isLeader(r: Role): bool = r == Leader
  action init = all { role' = Follower }
  action setLeader = all { role' = Leader }
  action step = any { setLeader }
}
