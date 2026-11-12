// Corpus-derived cells: an int-typed constant (non-proposition) and
// a bounded-int `and` proposition, from a real production spec.
module Ql006CorpusShapes {
  pure def DAB: int = 2
  val dBounded = and { DAB >= 0, DAB <= 3 }
}
