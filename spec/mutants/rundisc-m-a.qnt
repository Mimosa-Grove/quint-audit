// rundisc.qnt - the three-state run discipline for the quint-audit
// verification core: classifying a quint invocation as passed, failed or
// did-not-run from its observable facts, including the capture-layer
// masking shape (a crash inside a capture layer presents rc 0 AND empty
// output). The contract is stated in ./README.md. AGPLv3 - see ../LICENSE.
module rundisc {

  // The observable facts of one quint invocation, as the harness sees them
  // after any capture layer. rc: "zero" | "nonzero" | "none" (killed - no
  // exit code observable). successSummary/failureSummary: the run's own
  // summary lines present in the output. emptyOutput: the capture layer's
  // report was empty - the masked-crash presentation.
  type Facts = { rc: str, timedOut: bool, successSummary: bool, failureSummary: bool, emptyOutput: bool }

  pure def Bools: Set[bool] = Set(true, false)

  // The bounded verification domain: the full cross product of observable
  // facts (3 rc values x 16 summary/timeout/empty combinations = 48),
  // decoded from integers because 0.33 sets have no flatMap.
  pure def rcOf(i: int): str =
    if (i == 0) "zero" else if (i == 1) "nonzero" else "none"

  pure def bit(k: int, w: int): bool = ((k / w) % 2) == 1

  pure def factOf(k: int): Facts = {
    rc: rcOf(k / 16),
    timedOut: bit(k, 1),
    successSummary: bit(k, 2),
    failureSummary: bit(k, 4),
    emptyOutput: bit(k, 8)
  }

  pure def FactUniverse: Set[Facts] = 0.to(47).map(k => factOf(k))

  // named shapes used by the runs
  pure def f_clean_pass: Facts =
    { rc: "zero", timedOut: false, successSummary: true, failureSummary: false, emptyOutput: false }
  pure def f_clean_fail: Facts =
    { rc: "nonzero", timedOut: false, successSummary: false, failureSummary: true, emptyOutput: false }
  // the masked-crash shape: rc 0 as the capture layer reports it, empty output
  pure def f_masked_crash: Facts =
    { rc: "zero", timedOut: false, successSummary: false, failureSummary: false, emptyOutput: true }
  pure def f_zero_no_summary: Facts =
    { rc: "zero", timedOut: false, successSummary: false, failureSummary: false, emptyOutput: false }
  pure def f_nonzero_no_summary: Facts =
    { rc: "nonzero", timedOut: false, successSummary: false, failureSummary: false, emptyOutput: false }
  pure def f_timeout: Facts =
    { rc: "none", timedOut: true, successSummary: false, failureSummary: false, emptyOutput: false }
  pure def f_missing_binary: Facts =
    { rc: "none", timedOut: false, successSummary: false, failureSummary: false, emptyOutput: false }

  // The classifier: `passed` requires rc 0 AND the run's own success
  // summary on non-empty output; `failed` requires rc != 0 AND the run's
  // own failure summary on non-empty output; everything else - the
  // masked-crash shape, a timeout, a kill (rc none), and any run whose own
  // proof summary is missing - is `did-not-run`. Contradictory
  // observables (a summary claimed on empty output) are refused, never
  // passed.
  // MUTANT m-a: rc 0 alone is sufficient for passed - the summary and
  // non-empty-output requirements are dropped.
  pure def classifyRun(f: Facts): str =
    if (f.timedOut) "did-not-run"
    else if (f.rc == "zero") "passed"
    else if (and { f.rc == "nonzero", f.failureSummary, not(f.emptyOutput) }) "failed"
    else "did-not-run"

  // The verdict layer: only a failed run produces a lint verdict (only
  // `failed` can produce a lint finding); `did-not-run` is exit code 2 and
  // produces no verdict at all.
  pure def verdictOf(f: Facts): str =
    if (classifyRun(f) == "failed") "verdict" else "none"

  // the state machine: walks the fact universe so `quint run` exercises
  // the classifier; the invariants below are universe-quantified and hold
  // at every state regardless of the walk
  var facts: Facts

  action init = all {
    nondet f = FactUniverse.oneOf()
    facts' = f
  }

  action step = any {
    all {
      nondet f = FactUniverse.oneOf()
      facts' = f
    },
    facts' = facts
  }

  action setFacts(f) = facts' = f

  // the contract runs: each pins one classification fact the OCaml
  // implementation must mirror; the spec mutants die here (and under
  // `quint run --invariant`, never only one instrument)
  run r_clean_pass = setFacts(f_clean_pass).expect(classifyRun(facts) == "passed")
  run r_clean_fail = setFacts(f_clean_fail).expect(classifyRun(facts) == "failed")
  run r_masked_crash_did_not_run = setFacts(f_masked_crash).expect(classifyRun(facts) == "did-not-run")
  run r_zero_no_summary_did_not_run = setFacts(f_zero_no_summary).expect(classifyRun(facts) == "did-not-run")
  run r_nonzero_no_summary_did_not_run = setFacts(f_nonzero_no_summary).expect(classifyRun(facts) == "did-not-run")
  run r_timeout_did_not_run = setFacts(f_timeout).expect(classifyRun(facts) == "did-not-run")
  run r_missing_binary_did_not_run = setFacts(f_missing_binary).expect(classifyRun(facts) == "did-not-run")
  run r_failed_has_verdict = setFacts(f_clean_fail).expect(verdictOf(facts) == "verdict")
  run r_masked_crash_no_verdict = setFacts(f_masked_crash).expect(verdictOf(facts) == "none")
  run r_timeout_no_verdict = setFacts(f_timeout).expect(verdictOf(facts) == "none")

  // the contract invariants (I-*), universe-quantified so every state of
  // every bounded run checks every combination of observables. Verified
  // bounded via `quint run`; recorded as bounded, never claimed as proofs.

  // I-TOTAL: every combination of observable facts classifies to exactly
  // one state - exhaustive over the domain, exclusive by counting the
  // states the classifier can return for it
  val i_total = FactUniverse.forall(f =>
    Set("passed", "failed", "did-not-run").filter(s => classifyRun(f) == s).size() == 1)

  // I-PASSED-REQUIRES-PROOF: passed needs rc 0 AND the run's own success
  // summary; the masked-crash shape (rc 0 with empty output) is never passed
  val i_passed_requires_proof = FactUniverse.forall(f =>
    and {
      implies(classifyRun(f) == "passed", and { f.rc == "zero", f.successSummary }),
      implies(and { f.rc == "zero", f.emptyOutput }, classifyRun(f) != "passed")
    })

  // I-FAILED-REQUIRES-PROOF: failed needs rc != 0 AND the run's own
  // failure summary
  val i_failed_requires_proof = FactUniverse.forall(f =>
    and {
      implies(classifyRun(f) == "failed", and { f.rc == "nonzero", f.failureSummary }),
      implies(and { f.rc == "nonzero", not(f.failureSummary) }, classifyRun(f) != "failed")
    })

  // I-NO-VERDICT: did-not-run produces no lint verdict - the verdict
  // outcome and did-not-run are disjoint, and only failed carries one
  val i_no_verdict = FactUniverse.forall(f =>
    iff(verdictOf(f) == "verdict", classifyRun(f) == "failed"))

  // I-TIMEOUT: a timed-out run is did-not-run, never failed (a timeout is
  // not a pass and not a kill)
  val i_timeout = FactUniverse.forall(f =>
    implies(f.timedOut, classifyRun(f) == "did-not-run"))
}
