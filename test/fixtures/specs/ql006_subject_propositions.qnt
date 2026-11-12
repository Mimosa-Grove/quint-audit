// Genuine boolean tautologies that stay
// subjects - a declared bool, an Eq proposition, a Not proposition.
module Ql006SubjectPropositions {
  val t: bool = true
  val eqProp = 1 == 1
  pure def notFalse = not(false)
}
