// Declarations that are not propositions: an untyped literal set, a set
// constant and a typed string constant.
module Ql006SubjectConstants {
  type Dir = str

  pure def UNKNOWN: str = "unknown"
  pure def LAB: Set[str] = Set("a", "b")
  val Cols = Set("a", "b", "c")
  pure def E: Dir = ""
}
