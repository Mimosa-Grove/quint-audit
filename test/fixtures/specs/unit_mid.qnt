// Fixture: the middle of a two-level import chain.
module UnitMid {
  import UnitLeaf.* from "./unit_leaf"
  pure def midEcho = leafReads
}
