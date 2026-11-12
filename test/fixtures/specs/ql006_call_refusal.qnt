module Ql006CallRefusal {
  var resourceManagers: int
  def consistencyInv(rm: int): bool = rm == resourceManagers
  val inv: bool = consistencyInv(resourceManagers)
  action init = all { resourceManagers' = 0 }
  action step = any { all { resourceManagers' = resourceManagers } }
}
