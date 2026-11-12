// Fixture: a stepless helper module imported by a runnable spec.
module UnitHelper {
  var h: int
  pure def hReads = h
  pure def hSucc = h + 1
}
