// rundisc.qnt - the three-state run discipline for the quint-audit
// verification core: classifying a quint invocation as passed, failed or
// did-not-run from its observable facts, including the capture-layer
// masking shape (a crash inside a capture layer presents rc 0 AND empty
// output). The contract is stated in ./README.md. AGPLv3 - see ../LICENSE.
module rundisc {

  // The enum vocabulary: every symbolic string the contract compares or
  // returns is a named constant (the QL002 rule, followed by construction -
  // no comparison reads a raw literal).
  pure def RC_ZERO: str = "zero"
  pure def RC_NONZERO: str = "nonzero"
  pure def RC_NONE: str = "none"

  pure def S_PASSED: str = "passed"
  pure def S_FAILED: str = "failed"
  pure def S_DID_NOT_RUN: str = "did-not-run"
  pure def S_NOT_EVIDENCE: str = "not-evidence"

  pure def V_VERDICT: str = "verdict"
  pure def V_NONE: str = "none"

  pure def B_RUST: str = "rust"
  pure def B_TYPESCRIPT: str = "typescript"
  pure def B_UNPINNED: str = ""

  // The observable facts of one quint invocation, as the harness sees them
  // after any capture layer. rc: zero | nonzero | none (killed - no
  // exit code observable). successSummary/failureSummary: the run's own
  // summary lines present in the output. emptyOutput: the capture layer's
  // report was empty - the masked-crash presentation.
  type Facts = { rc: str, timedOut: bool, successSummary: bool, failureSummary: bool, emptyOutput: bool }

  pure def Bools: Set[bool] = Set(true, false)

  // The bounded verification domain: the full cross product of observable
  // facts (3 rc values x 16 summary/timeout/empty combinations = 48),
  // decoded from integers because 0.33 sets have no flatMap.
  pure def rcOf(i: int): str =
    if (i == 0) RC_ZERO else if (i == 1) RC_NONZERO else RC_NONE

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
    { rc: RC_ZERO, timedOut: false, successSummary: true, failureSummary: false, emptyOutput: false }
  pure def f_clean_fail: Facts =
    { rc: RC_NONZERO, timedOut: false, successSummary: false, failureSummary: true, emptyOutput: false }
  // the masked-crash shape: rc 0 as the capture layer reports it, empty output
  pure def f_masked_crash: Facts =
    { rc: RC_ZERO, timedOut: false, successSummary: false, failureSummary: false, emptyOutput: true }
  pure def f_zero_no_summary: Facts =
    { rc: RC_ZERO, timedOut: false, successSummary: false, failureSummary: false, emptyOutput: false }
  pure def f_nonzero_no_summary: Facts =
    { rc: RC_NONZERO, timedOut: false, successSummary: false, failureSummary: false, emptyOutput: false }
  pure def f_timeout: Facts =
    { rc: RC_NONE, timedOut: true, successSummary: false, failureSummary: false, emptyOutput: false }
  pure def f_missing_binary: Facts =
    { rc: RC_NONE, timedOut: false, successSummary: false, failureSummary: false, emptyOutput: false }

  // The classifier: `passed` requires rc 0 AND the run's own success
  // summary on non-empty output; `failed` requires rc != 0 AND the run's
  // own failure summary on non-empty output; everything else - the
  // masked-crash shape, a timeout, a kill (rc none), and any run whose own
  // proof summary is missing - is `did-not-run`. Contradictory
  // observables (a summary claimed on empty output) are refused, never
  // passed.
  pure def classifyRun(f: Facts): str =
    if (f.timedOut) S_DID_NOT_RUN
    else if (and { f.rc == RC_ZERO, f.successSummary, not(f.emptyOutput) }) S_PASSED
    else if (and { f.rc == RC_NONZERO, f.failureSummary, not(f.emptyOutput) }) S_FAILED
    else S_DID_NOT_RUN

  // The verdict layer: only a failed run produces a lint verdict (only
  // `failed` can produce a lint finding); `did-not-run` is exit code 2 and
  // produces no verdict at all.
  pure def verdictOf(f: Facts): str =
    if (classifyRun(f) == S_FAILED) V_VERDICT else V_NONE

  // The backend-provenance layer. The three-state
  // classifier is over one invocation's observable facts, but the same facts
  // mean different things per backend: a false `init` on TypeScript is
  // reported as [ok] with rc 0 and non-empty output - the exact shape
  // classified `passed`. An init PASS therefore requires Rust evidence. An
  // init ERROR is observable on both backends, so a TypeScript failure stays
  // evidence. An unpinned backend is never evidence. The contract, stated in
  // ./README.md: an init pass is Rust evidence only, an init error is evidence
  // on both backends, and an unpinned backend is never evidence.
  pure def BackendUniverse: Set[str] = Set(B_RUST, B_TYPESCRIPT, B_UNPINNED)

  pure def initVerdict(backend: str, f: Facts): str =
    if (backend == B_TYPESCRIPT and classifyRun(f) == S_PASSED) S_NOT_EVIDENCE
    else if (backend == B_RUST or backend == B_TYPESCRIPT) classifyRun(f)
    else S_NOT_EVIDENCE

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
    }
  }

  // the contract runs: each pins one classification fact the OCaml
  // implementation must mirror; the spec mutants die here (and under
  // `quint run --invariant`, never only one instrument)
  run r_clean_pass = all { facts' = f_clean_pass }.expect(classifyRun(facts) == S_PASSED)
  run r_clean_fail = all { facts' = f_clean_fail }.expect(classifyRun(facts) == S_FAILED)
  run r_masked_crash_did_not_run = all { facts' = f_masked_crash }.expect(classifyRun(facts) == S_DID_NOT_RUN)
  run r_zero_no_summary_did_not_run = all { facts' = f_zero_no_summary }.expect(classifyRun(facts) == S_DID_NOT_RUN)
  run r_nonzero_no_summary_did_not_run = all { facts' = f_nonzero_no_summary }.expect(classifyRun(facts) == S_DID_NOT_RUN)
  run r_timeout_did_not_run = all { facts' = f_timeout }.expect(classifyRun(facts) == S_DID_NOT_RUN)
  run r_missing_binary_did_not_run = all { facts' = f_missing_binary }.expect(classifyRun(facts) == S_DID_NOT_RUN)
  run r_failed_has_verdict = all { facts' = f_clean_fail }.expect(verdictOf(facts) == V_VERDICT)
  run r_masked_crash_no_verdict = all { facts' = f_masked_crash }.expect(verdictOf(facts) == V_NONE)
  run r_timeout_no_verdict = all { facts' = f_timeout }.expect(verdictOf(facts) == V_NONE)
  // backend provenance: an init pass is Rust evidence only; a
  // TypeScript pass is not evidence; a TypeScript failure (init error) is
  run r_init_rust_pass = all { facts' = f_clean_pass }.expect(initVerdict(B_RUST, facts) == S_PASSED)
  run r_init_ts_pass_not_evidence = all { facts' = f_clean_pass }.expect(initVerdict(B_TYPESCRIPT, facts) == S_NOT_EVIDENCE)
  run r_init_ts_error_failed = all { facts' = f_clean_fail }.expect(initVerdict(B_TYPESCRIPT, facts) == S_FAILED)
  run r_init_unpinned_not_evidence = all { facts' = f_clean_pass }.expect(initVerdict(B_UNPINNED, facts) == S_NOT_EVIDENCE)

  // the contract invariants (I-*), universe-quantified so every state of
  // every bounded run checks every combination of observables. Verified
  // bounded via `quint run`; recorded as bounded, never claimed as proofs.

  // I-TOTAL: every combination of observable facts classifies to exactly
  // one state - exhaustive over the domain, exclusive by counting the
  // states the classifier can return for it
  val i_total = FactUniverse.forall(f =>
    Set(S_PASSED, S_FAILED, S_DID_NOT_RUN).filter(s => classifyRun(f) == s).size() == 1)

  // I-PASSED-REQUIRES-PROOF: passed needs rc 0 AND the run's own success
  // summary; the masked-crash shape (rc 0 with empty output) is never passed
  val i_passed_requires_proof = FactUniverse.forall(f =>
    and {
      implies(classifyRun(f) == S_PASSED, and { f.rc == RC_ZERO, f.successSummary }),
      implies(and { f.rc == RC_ZERO, f.emptyOutput }, classifyRun(f) != S_PASSED)
    })

  // I-FAILED-REQUIRES-PROOF: failed needs rc != 0 AND the run's own
  // failure summary
  val i_failed_requires_proof = FactUniverse.forall(f =>
    and {
      implies(classifyRun(f) == S_FAILED, and { f.rc == RC_NONZERO, f.failureSummary }),
      implies(and { f.rc == RC_NONZERO, not(f.failureSummary) }, classifyRun(f) != S_FAILED)
    })

  // I-NO-VERDICT: did-not-run produces no lint verdict - the verdict
  // outcome and did-not-run are disjoint, and only failed carries one
  val i_no_verdict = FactUniverse.forall(f =>
    iff(verdictOf(f) == V_VERDICT, classifyRun(f) == S_FAILED))

  // I-TIMEOUT: a timed-out run is did-not-run, never failed (a timeout is
  // not a pass and not a kill)
  val i_timeout = FactUniverse.forall(f =>
    implies(f.timedOut, classifyRun(f) == S_DID_NOT_RUN))

  // I-INIT-PASS-REQUIRES-RUST: an init pass is Rust evidence only
  val i_init_pass_requires_rust = BackendUniverse.forall(b => FactUniverse.forall(f =>
    implies(initVerdict(b, f) == S_PASSED, b == B_RUST)))

  // I-TS-PASS-NOT-EVIDENCE: the TypeScript [ok] shape cannot carry an init
  // pass - the same facts are what a false init reports there
  val i_ts_pass_not_evidence = FactUniverse.forall(f =>
    implies(classifyRun(f) == S_PASSED, initVerdict(B_TYPESCRIPT, f) == S_NOT_EVIDENCE))

  // I-INIT-ERROR-BOTH: an init error (a classified failure) is evidence on
  // both backends
  val i_init_error_both = FactUniverse.forall(f =>
    implies(classifyRun(f) == S_FAILED, and {
      initVerdict(B_RUST, f) == S_FAILED,
      initVerdict(B_TYPESCRIPT, f) == S_FAILED
    }))

  // I-UNPINNED-NOT-EVIDENCE: an unpinned backend produces no evidence
  val i_unpinned_not_evidence = FactUniverse.forall(f =>
    initVerdict(B_UNPINNED, f) == S_NOT_EVIDENCE)
}
