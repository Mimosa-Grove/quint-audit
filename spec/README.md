# Verification-core specifications

Three Quint specifications for the quint-audit verification core, written
spec-first: the OCaml implementation reads these before writing code.
The product contract they implement is summarised in `../README.md`;
the per-spec statements below are the authority for each calculus.

- `qcalc.qnt` - the QP001 classification calculus. Models boolean
  property bodies as fixed-depth trees over literals, leaf variables,
  the connectives `and or not implies iff`, `eq`/`neq` over subtrees
  and a spine marker for unmodelled structure. The classifier is the
  truth-table calculus: it enumerates the assignments of the free
  leaves (every distinct variable, plus every `eq`/`neq` node whose
  subtrees are not canonically identical, as an opaque leaf) and
  returns `const-true`, `const-false`, `varies` or `unknown`. The
  downstream decision passes only `varies`.
- `rundisc.qnt` - the three-state run discipline. Models the
  observable facts of one quint invocation (exit-code class zero /
  nonzero / none, the run's own success and failure summaries, a
  timeout and the capture layer's empty report) and the classifier
  that maps them to `passed` / `failed` / `did-not-run`, plus the
  verdict layer that only `failed` can reach.
- `irdecode.qnt` - the typed-IR decode contract. Models the
  source map as spans that name their source (main or imported), the
  per-source module extent, the declaration kinds 0.33.1 emits and
  the reporting-set/census split; plus the two report-health
  properties (no pass on junk-valued evidence, refused states
  disclosed). The contract is written against real decode shapes:
  imported spans and module extents, the nameless `import`/`instance`
  declarations, `assume` and the non-ASCII precondition.

## Not modelled

- Parsing and the typed IR. The tree shape is fixed-depth; the
  implementation reads bodies from quint's parse output. The
  `actionAll`/`actionAny` to `and`/`or` mapping happens before the
  calculus and is an implementation-side preprocessing step.
- Unbounded trees, name resolution and operators beyond the contract
  list. The spine marker stands for every unmodelled spine, and an
  operator outside the recognition set is a refusal, never a pass.
- `quint verify` beyond the recorded depth-2 cells, Apalache and temporal
  properties. The recorded instruments are bounded simulation plus
  run-level tests, with the depth-2 verify cells as a bounded
  cross-check, not a proof method.
- Fuzzing beyond the fixed domains. The qcalc invariants are quantified
  over a fixed 18-body pool; the rundisc invariants over the full
  48-combination cross product of observable facts. The invariants are
  domain-quantified, so every state of every bounded trace checks the
  entire domain - and the result is still recorded as bounded.

## Bounded verification record

quint 0.33.1, simulator backend (`quint run`) and Apalache (0.62.4, via
`quint verify`, bounded). Every "no violation found" below means no
counterexample was observed in the runs executed; none of it is a proof.
`quint verify` is reported at its stated step bound. Bounds everywhere:
`--max-steps=30 --max-samples=100` for run cells; `--max-steps=2` for
the verify cells.

The three specs are restructured to lint clean under quint-audit itself -
every symbolic string the contracts compare or return is a named
constant (the QL002 rule, followed by construction), the no-op stutter
branches are out of `step`, the thin delegating actions (setBody,
setFacts, setTick) are inlined into their runs, and `irdecode.qnt`'s flat
18-val `i_contract` is grouped into two vals, each carrying the tick walk
as an antecedent (true in every reachable state) so the state dependency
is explicit and the free-leaf count is inside the truth table's bound.
Verification covers typecheck, the run tables above, the depth-2 verify
cells (including qcalc's five and rundisc's nine invariants, recorded
below), all seven mutant kills under both instruments and the instrument
check - all green. The lints over all three specs return rc 0 with zero
rows.

Base specs, all green:

| command | rc | result |
|---|---|---|
| `quint typecheck spec/qcalc.qnt` | 0 | clean |
| `quint typecheck spec/rundisc.qnt` | 0 | clean |
| `quint test spec/qcalc.qnt --match='^r_'` | 0 | 15 passing |
| `quint test spec/rundisc.qnt --match='^r_'` | 0 | 14 passing |
| `quint typecheck spec/irdecode.qnt` | 0 | clean |
| `quint test spec/irdecode.qnt --match='^r_'` | 0 | 11 passing |
| `quint verify spec/irdecode.qnt --invariant=i_contract --max-steps=2` | 0 | `[ok] No violation found` (Apalache 0.62.4) |
| `quint verify spec/qcalc.qnt --invariants i_exhaustive i_sound_true i_sound_false i_refuse_unknown i_eq_identity --max-steps=2` | 0 | `[ok] No violation found` (Apalache 0.62.4) |
| `quint verify spec/rundisc.qnt --invariants i_total i_passed_requires_proof i_failed_requires_proof i_no_verdict i_timeout i_init_pass_requires_rust i_ts_pass_not_evidence i_init_error_both i_unpinned_not_evidence --max-steps=2` | 0 | `[ok] No violation found` (Apalache 0.62.4) |

The adopted verify depth for `irdecode.qnt` is 2. Depths 2, 4 and 8 all
return `[ok] No violation found` with all 18 invariants holding, so 4 and
8 are decoration and the working depth is the shallowest stable one, 2.
Depth 2 is green on the grouped form, which carries the 18 component
invariants verbatim inside `i_source_map_contract` and
`i_decl_kind_report_contract`. The instrument is tested, not just green:
a planted `spanDecision` mutation (an imported span past its own source
decodes) is killed at depth 2 by `i_no_silent_wrong_span`.

Invariants, each verified with
`quint run spec/<spec>.qnt --invariant=<name> --max-steps=30 --max-samples=100`
(every one rc 0, `[ok] No violation found`):

| spec | invariant | statement |
|---|---|---|
| qcalc | `i_exhaustive` | a modelled-spine body is never `unknown` |
| qcalc | `i_sound_true` | `const-true` is true under every assignment |
| qcalc | `i_sound_false` | `const-false` is false under every assignment |
| qcalc | `i_refuse_unknown` | `unknown` is a refusal, never a pass |
| qcalc | `i_eq_identity` | `eq(P,P)` is `const-true`; `eq(P,Q)` distinct is `varies` |
| rundisc | `i_total` | every observable combination hits exactly one state |
| rundisc | `i_passed_requires_proof` | `passed` needs rc 0 and the success summary; rc 0 with empty output is never `passed` |
| rundisc | `i_failed_requires_proof` | `failed` needs rc != 0 and the failure summary |
| rundisc | `i_no_verdict` | only `failed` carries a lint verdict |
| rundisc | `i_timeout` | a timeout is `did-not-run`, never `failed` |
| rundisc | `i_init_pass_requires_rust` | an init pass is Rust evidence only |
| rundisc | `i_ts_pass_not_evidence` | the TypeScript `[ok]` shape cannot carry an init pass |
| rundisc | `i_init_error_both` | an init error is evidence on both backends |
| rundisc | `i_unpinned_not_evidence` | an unpinned backend produces no evidence |

## Mutant table

Each mutant is a fixture cut from its spec with one planted mutation.
The rundisc m-a/m-b/m-c cuts predate the init-evidence layer. A kill
requires both instruments: a violation of the named invariant under
`quint run` (bounded, trace saved) and a failure of the spec's own runs
under `quint test`. One instrument alone is not a kill. All seven kills
are rc 1 on both instruments.

Kill commands, both rc 1 for every row:

```
quint run spec/mutants/<mutant>.qnt --invariant=<invariant> --max-steps=30 --max-samples=100
quint test spec/mutants/<mutant>.qnt --match='^r_'
```

| mutant | planted mutation | invariant violated | run(s) killed | trace |
|---|---|---|---|---|
| `mutants/qcalc-m-a.qnt` | `implies` dropped from the recognition set: a tautology over `implies` becomes `unknown` | `i_exhaustive` | `r_implies_tautology` | `mutants/traces/qcalc-m-a-i_exhaustive.txt` |
| `mutants/qcalc-m-b.qnt` | `unknown` mapped to the pass lane | `i_refuse_unknown` | `r_spine_refused` | `mutants/traces/qcalc-m-b-i_refuse_unknown.txt` |
| `mutants/qcalc-m-c.qnt` | body-level `eq` identity rule dropped: `eq` is always a free leaf | `i_eq_identity` | `r_eq_identity`, `r_eq_node_identity` | `mutants/traces/qcalc-m-c-i_eq_identity.txt` |
| `mutants/rundisc-m-a.qnt` | rc 0 alone is sufficient for `passed` | `i_passed_requires_proof` | `r_masked_crash_did_not_run`, `r_zero_no_summary_did_not_run` | `mutants/traces/rundisc-m-a-i_passed_requires_proof.txt` |
| `mutants/rundisc-m-b.qnt` | a timeout classifies as `failed` | `i_timeout` | `r_timeout_did_not_run`, `r_timeout_no_verdict` | `mutants/traces/rundisc-m-b-i_timeout.txt` |
| `mutants/rundisc-m-c.qnt` | `did-not-run` produces a verdict | `i_no_verdict` | `r_masked_crash_no_verdict`, `r_timeout_no_verdict` | `mutants/traces/rundisc-m-c-i_no_verdict.txt` |
| `mutants/rundisc-m-d.qnt` | the backend gate is dropped: a TypeScript `[ok]` shape is accepted as an init pass | `i_init_pass_requires_rust`, `i_ts_pass_not_evidence` | `r_init_ts_pass_not_evidence`, `r_init_unpinned_not_evidence` | `mutants/traces/rundisc-m-d-i_init_pass_requires_rust.txt` |

Per-mutant run outputs: `mutants/traces/<mutant>-runs.txt`. Each trace
file carries the counterexample state, the simulator seed for
reproduction and `error: Invariant violated`.

Every surviving mutant check passed in the expected direction too: on
the base specs all runs named above are green, so each red is the
mutation, not a fixture bug.

## Mirrored tests

These specifications implement no OCaml. The property tests that mirror
them are pinned in the shapes here:

- The QP001 check (the truth-table check over the decoded IR) carries
  property tests asserting the five qcalc invariants against the OCaml
  classifier, plus fixtures shaped like the qcalc runs: the
  `implies(x,x)` tautology, `or(x, not(x))`, `and(x, not(x))`,
  `iff(x, not(x))`, `eq(P,P)`, `eq(P,Q)` over distinct subtrees and
  the spine refusal.
- The three-state classifier (in the run-driving checks)
  carries property tests asserting the five rundisc invariants over the
  observable-fact cross product, plus fixtures shaped like the rundisc
  runs: the masked-crash shape (rc 0 with empty output) first, then
  rc 0 without a summary, rc != 0 without a summary, the timeout and
  the missing binary. The backend-provenance layer adds the
  `initVerdict` mirror over the 2 x 48 domain, the four
  named init runs and the backend-gate mutant as the regression
  fixture.
- The mutants double as regression fixtures: each planted mutation is
  a defect class the mirrored tests must catch on the implementation
  side.

## Maintainer notes (quint 0.33.1)

Facts that shaped these specs and will shape their maintenance:

- No recursive definitions (QNT099): use `fold`. No set `flatMap` or
  `toList`. No string concatenation: leaf identity is structural (a
  tagged record with `==`), which is also why the eq-leaf names cannot
  collide.
- `if (c) a else b` with the parentheses and without `then`; `not(x)`
  parenthesised; set membership is `.in(s)` or `.exists(e => e == x)`.
- `--match` on `quint test` is an unanchored regex: anchor it (`'^r_'`)
  or it also selects declarations whose names merely contain the
  pattern. A bare `quint test` selects zero runs and exits 0.
- `.then` chains require a matching effect signature across the
  composed actions; assertion runs therefore end in `.expect(...)`.
- `quint run` without `--seed` samples up to 10000 traces by default;
  domain-quantified invariants are heavy per state, so the record pins
  `--max-samples=100`.
- `--seed` changes the sample default to 1, not just the trace choice:
  a seeded run without an explicit `--max-samples` explores one trace.
  Any seeded cell passes both flags (quint 0.33.1, `cli.ts:450-453`).
- `quint run --verbosity=0` prints nothing on a clean run (verified:
  rc 0, zero bytes); the `[ok]` summary appears at level 1.
  The three-state classifier needs that summary, so classification is done at
  level 1 and level 0 is reserved for the false-init discriminator:
  a false init prints `error: Invariant violated` there, while levels
  1 and 2 crash while printing the counterexample.
