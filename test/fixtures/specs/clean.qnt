module Clean {
  type Role = | Leader | Follower
  const LIMIT: int
  var role: Role
  var x: int
  pure def inc(v: int): int = v + 1
  pure def isLeader(r: Role): bool = r == Leader
  val bound = x > 0 and x < 100
  val hasRole = isLeader(role)
  action init = all { role' = Follower, x' = 0 }
  action advance = all { x >= 0, x' = inc(x), role' = role }
  action setLeader = all { isLeader(role) implies x > 0, role' = Leader, x' = x }
  action step = any { advance, setLeader }
}
