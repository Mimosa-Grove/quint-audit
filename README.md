# quint-audit

A deterministic linter for Quint specifications. `quint-audit` reads an
existing `.qnt` file, decodes quint's own parse IR into typed OCaml
structures, and reports structural findings. No LLM is involved. No
`quint verify` is invoked.

Specifications audited, proofs grafted.

Status: v0.1.0. Check ids, exit codes and the report schema are the stable contract. The check semantics are modelled in Quint and verified with killed mutants. Every check was adversarially reviewed against a 67-spec real corpus. Remaining provisional through v0.x: individual severities and message wording, which may move as the corpus grows.

## What it does

[Quint Studio](https://quint.sh/product) runs quality checks on the specs it generates, but so far it cannot
see hand-written specs. The Quint team has stated there is currently no conversion
path from an existing `.qnt` file into Studio's component shape.

`quint-audit` runs the [Quint LLM
kit](https://github.com/quint-co/quint-llm-kit) review checklist
against any existing `.qnt` spec, and adds checks for production
pitfalls the checklist does not cover. The names of the checks and the
rows of the report follow that checklist, so the output should read
familiarly to the Quint community. Findings
carry spans, severities, suggestions and exit codes, in a human report
and a stable JSON document. quint-audit has been built for CI.

## Why it exists

`quint verify` answers "does an invariant break within N steps?". It
cannot ask whether the spec is well built. An action that skips a
variable, a tautological invariant, a dead branch, a missing witness:
none of these is a model-checking question. A spec can verify green and
still be vacuous or unmaintainable. `quint-audit` asks the build-discipline
questions, at parse cost.

The Quint LLM kit's review is a model's judgement on one spec at a time; quint-audit
is a deterministic checker, and an IR run gives byte-identical
findings for the same input and flags. Its check semantics are modelled in Quint,
verified in this repository and exercised by killed mutants. The LLM kit's
checklist is prose the model interprets. `quint-audit` follows the import
graph, attributes findings to the file that owns each one and
deduplicates; it runs at parse cost in CI, with exit codes, a JSON
schema, stable check ids and no model in the loop. The LLM kit's review is
deeper interactively: it drives the REPL, shows the state at a
violation, carries the per-action witnesses check and the conversational
fix loop; `quint-audit` is the fleet instrument beside it, not a
replacement.

|  | `quint verify` | Quint Studio checks | quint-audit | LLM kit review |
|---|---|---|---|---|
| what | bounded model checking via Apalache or TLC | quality review in the Studio app, on the specs it generates | static audit of any existing `.qnt` spec | LLM review of one finished spec |
| question | does an invariant break within N steps? | is the generated model well built? | does the spec follow the modelling discipline? | the same build-discipline question, read by a model |
| input | a typechecked spec | a spec built in Studio | any `.qnt` file | one `.qnt` file |
| output | counterexample or no-violation-in-bounds | review notes in the editor | findings with spans, severities, exit codes, JSON | a review report with fixes, from model judgement |
| where | CLI, local or CI | desktop app, GUI and terminal UI | CLI, designed for CI gates | an LLM agent, interactively |
| cost | minutes to hours per spec | interactive | about the parse time per spec | model tokens, per spec |

## How it works

1. `quint-audit` reads the spec bytes. A non-ASCII source is refused with
   the first offending byte offset. The source map indices are UTF-16
   code units; a non-ASCII character shifts every later span, so spans
   would stop naming the bytes they report.
2. It runs `quint parse --out <ir.json> --source-map <map.json>` under a
   60 s timeout. A parse failure is exit 2, never a lint report.
3. A typed decoder validates every consumed IR field. A malformed IR is
   a decode failure naming the JSON field path. The decoder never
   substitutes a default for a consumed field. Unknown IR node kinds are
   preserved: a check that needs one reports an `info` coverage gap,
   never a pass.
4. The IR checks run per module. Name resolution is module-local.
5. In `full`, the run-driving checks sample traces under a three-state
   discipline: `passed` requires exit code 0 and the run's own success
   summary; `failed` requires a failure summary; everything else is
   `did-not-run` and exit 2. A timeout is not a pass.
6. The report prints, and the process exits 0, 1 or 2.

## Install

From source. You need OCaml 5.3, dune and opam.

```sh
opam install . --yes
```

Or build without installing:

```sh
opam exec -- dune build
# binary: _build/default/bin/quint_audit_cli.exe
```

Quint itself is a runtime dependency. Install quint 0.33.1:

```sh
npm i @informalsystems/quint@0.33.1 -g
```

`quint-audit` finds `quint` on PATH, or takes an explicit path with
`--quint /path/to/quint`.

Supported quint version: 0.33.1. The pin exists because the typed decoder
is written against that release's parse-IR shape. The tool records
quint's version string in the report; it never compares it. A newer quint
that keeps the consumed fields still works. One that moves a field fails
loudly: the decode error names the JSON path, and the process exits 2.
The development corpus (see Verification) is the wider drift detector:
every check change is swept over 67 real specs before it lands.

## Usage

```sh
quint-audit lint path/to/spec.qnt
quint-audit lint --format=json path/to/spec.qnt
quint-audit lint --fail-on=warn path/to/spec.qnt
quint-audit lint --quint /path/to/quint path/to/spec.qnt

quint-audit full path/to/spec.qnt
quint-audit full --max-samples 10 --max-steps 20 --seed 0x2 \
  --invariant=i_safety path/to/spec.qnt
```

- `lint` runs the deterministic IR checks: QL001, QL002, QL003, QL006,
  QL008, QL009, QP001, QP002.
- `full` adds the run-driving checks: QL004 witnesses, the QL007 init
  execution, QL010 invariants at init, QL011 invariants after actions.
- Every `quint run` is pinned: backend, verbosity, an explicit sample
  count and an explicit step bound. The pins print with the report. A
  seeded run still passes the sample count explicitly, because quint
  drops its default to 1 when a seed is supplied.
- `--invariant NAME` (repeatable) names `val` declarations to evaluate
  as invariants. When no name is supplied, nothing is evaluated: QL010
  and QL011 report not-evaluated and never pass by default.
- `--run-timeout SECONDS` bounds one quint run (default 120).

### Exit codes

| code | meaning |
|---|---|
| 0 | no finding at or above the gate threshold |
| 1 | at least one finding at or above the threshold. The default threshold is `fail`; `--fail-on=warn` lowers the threshold and also fails on warnings |
| 2 | the audit could not run: usage error, missing quint, non-ASCII input, parse failure, typed decode failure, a run that did not execute or an internal error |

Exit 2 never means a spec violation. A gate can distinguish "the spec
violates the rules" from "the linter could not run".

### Machine-readable output

`--format=json` emits a stable document. The schema ships as
[`docs/report-schema.json`](docs/report-schema.json). Field names are
fixed. `findings` is the flat, deduplicated list; `sources` carries the
same rows grouped by the file that owns them; `dedup` states the
emitted, reported and removed counts, so the report reconciles its own
counts. On IR runs (`lint`), the `findings` array and `summary` are
byte-identical across runs on the same input; `parse_ms` is a
wall-clock field and varies. A sampled run (`full`) is reproducible
only with an explicit `--seed`; without one, sampled findings vary
between runs by design.
The JSON contract is part of the product: CI gates parse it, not the
human text.

## CI example

A GitHub Actions job that fails on findings at or above the threshold.
Exit 2 also fails the job, which is the correct outcome: a linter that
could not run should not pass a gate.

```yaml
name: quint-audit
on: [pull_request]
jobs:
  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: 20
      - run: npm install -g @informalsystems/quint@0.33.1
      - uses: ocaml/setup-ocaml@v3
        with:
          ocaml-compiler: "5.3"
      - run: opam install . --yes
      - run: opam exec -- quint-audit lint spec/main.qnt
```

## Reading the report

The human report prints one block per module. A status line carries the
spec path, the module name, the quint version, the IR sha256, the parse
time and the mode.

```
-- Spec review: surface.qnt (module Surface) --
quint 0.33.1 | ir sha256 ... | parse 1556 ms | mode ir

Structural (vs the build discipline)
  thin actions                    QL001  [✓]
  enums over strings              QL002  [⚠ 2 issue(s)]
  ...
Runtime
  init assigns all vars           QL007  [skipped (requires run)]
  ...

Differentiator checks
  literal-false property          QP001  [✗ 1 issue(s)]
  ...
```

- A row shows a pass, a warn count, a fail count or a state in words:
  `deferred`, `skipped`. A skipped row is never shown as a pass.
- `Top issues` lists findings as
  `check source:line:col message (suggestion)`. The suggestion is a
  hint, never a patch.
- An `info` row is a coverage note: a part of the spec the checks could
  not read. It never affects the exit code.
- Every finding names its source file. A finding in an imported module
  names the imported file, with positions in that file.
- The file you name on the command line is the entry. Its parse IR
  already carries its transitive imports, so the entry is audited as
  one unit.
- Findings are attributed to the file that owns them, deduplicated at
  report assembly: a definition reached through two import paths is
  reported once, against its defining file.
- The step-reachability question (QL009) applies to the modules the
  file you named defines. A library module reached through an import
  is not asked for a `step`; its QL009 row is reported as `skipped` -
  the question was not asked of that module, and a skipped row is
  never a pass.

### Sampled results, never over-claimed

The run-driving checks sample traces. A violation is conclusive. The
absence of one is reported as "no counterexample observed in the runs
executed". The report states the run count, max steps, backend and seed
with every sampled result. The tool never says an invariant holds.

## Findings, walked through

Two rows from a real audit of a first-party spec (paths shortened).
`lint` on this file exits 1: one fail.

```
QL006 ticks.qnt:377:7 invariant references no state variable or
  constant (tautology over state) (assert a property of the model state)
QL006 ticks.qnt:363:7 invariant is a literal bound or type check only
  (add a structural invariant over the model state)
```

The QL009 warn row between these two is omitted from the excerpt.

The failing line:

```quint
val t1k = K_LO == 3 and K_HI == 20 and K_LO < K_HI
```

`K_LO` and `K_HI` are `pure def` declarations with literal bodies, so
QL006 traces every reference transitively and finds no state variable
and no constant. The property can never fail, so as an invariant it is
vacuous. It documents a ratified band, which is a comment's job. The
fix: state a property of the model state, or move the band note into a
comment.

The warn:

```quint
val t0 = pmin < pmax
```

`pmin` and `pmax` are state variables, so this property does read state.
But it only compares two atoms, so QL006 classifies it as a bound check:
a proxy, warn-only, stated as such in the row. The fix: add a structural
invariant over the model state, or accept the warn if the bound is the
intended property.

## The check catalogue

The baseline names match the
[Quint LLM kit](https://github.com/quint-co/quint-llm-kit)
`quint-modeling` review checklist, so a Quint community reader recognises
every row. Ids are additive and stable: `QLnnn` for the checklist
baseline, `QPnnn` for the production-pitfall additions. Ids are never
renumbered.

### IR checks (run by `lint`)

| id | detects | provenance | default severity | how to fix |
|---|---|---|---|---|
| QL001 | thin actions: an action body that is not an all/any composition; business logic embedded in an assignment; a no-op fallback branch; a call to a state-reading def | LLM kit checklist | warn | wrap guards and assignments in `all { ... }`; lift logic into a `pure def`; disable the unused action |
| QL002 | raw string literals compared with `eq`/`neq` or assigned into state, where a sum type is the modelling rule | LLM kit checklist | warn | model the choice as a sum type |
| QL003 | vars always assigned together across two or more actions: a record-grouping candidate | LLM kit checklist | warn | consider one record. The census is textual; a helper action's assignments are invisible |
| QL006 | invariants that assert nothing: a body referencing no state variable and no constant is a fail (tautology); const-only is a warn (premise-check candidate); an unanalysable dependency is a warn; a literal bound check only is a warn | LLM kit checklist | fail / warn | assert a property of the model state |
| QL008 | a leaf action that does not assign every var a primed value | LLM kit checklist | warn | add the suggested stutter `x' = x.` |
| QL009 | a module with no `step`; a step body that is not an `any` composition of action calls; an action not reachable from `step` | LLM kit checklist | warn | `action step = any { ... }`; add missing actions to the step branches |
| QP001 | property bodies that are constant `false` or constant `true` (void property), decided by a truth-table classification; an unclassifiable body is an `info` coverage gap | production pitfalls | fail | remove the contradiction; assert something that can fail |
| QP002 | a `pure def` or `pure val` that reads a state variable. quint's typechecker rejects the parameterised shapes (QNT200); the nullary `pure def` shape typechecks on 0.33.1, and this check catches it early, on parse-only input | production pitfalls | fail | make it a non-pure def, or pass the value as a parameter |

QL009 follows calls to module actions: reachability is the forward
closure of `step` over those calls, and a call cycle is traversed. A
`nondet` prefix decodes as a `let`, so the step shape is found through
let binders. The check classifies the modules defined in the file you
named: a module reached only through an import is not a runnable unit
and gets a `skipped` step-reachability row, not a pass.

### Run-driving checks (run by `full`)

| id | detects | provenance | default severity | how to fix |
|---|---|---|---|---|
| QL004 | no state-reading `val` can serve as a witness; a witness reached in zero sampled traces; an action never exercised in the sampled traces | LLM kit checklist | fail / warn | add witness vals that read state; exercise the flagged actions |
| QL007 | a module with no `init`; a var not assigned exactly once in `init`; an `init` that returns false or errors when executed | LLM kit checklist | fail | `action init = all { ... }` assigning every var exactly once |
| QL010 | an invariant that is false at the initial state, naming the invariant and quoting the state | LLM kit checklist | fail | fix the init state or the invariant |
| QL011 | an invariant violated after some action, naming the action, the invariant and the state. Sampled, per the wording rules above | LLM kit checklist | fail | fix the action or the invariant; stress-test with `quint run` |

QL004 zero counts are ambiguous by construction: zero also covers a
false `init`, a deadlock and a not-evaluated witness. The report says
so; a zero is never read as proof of a dead witness. The kit's
checklist asks for one witness per major action; that per-action
verdict is deferred (see Scope limits).

### Deferred and out of scope

- QL005 (right abstraction): not decidable over the IR. Deferred.
- QL004's per-action witness verdict (one witness per major action):
  witness presence and dead-witness detection ship in v0.1.0; the
  per-action mapping is deferred to v0.1.1 (see Scope limits).
- QP004 (a `val` after the module's closing brace): needs a source
  text scan. Deferred to v0.1.1.
- QP005-QP011: seven invocation, verify and environment properties,
  deferred: they need `quint verify`, the typechecker or the source
  text, not the parse IR. QP003 (forward references) is
  dead over quint 0.33.1: the parser toposorts declarations before the
  IR is written.

## Scope limits

- **No typechecking.** `lint` reads the parse IR only. A spec with a
  mode error can lint and exit 0: `val g = b`, where `b` is an action,
  parses and lints with no fail, while `quint typecheck` rejects it. Run
  `quint typecheck` separately; it is not this tool's job. QP002 catches
  one mode-error class early, on parse-only input; the rest are
  invisible here.
- **Runtime results are sampled, not exhaustive.** Only a violation is
  conclusive. Absence of a counterexample is never reported as a proof,
  and the run count, max steps, backend and seed print with every
  sampled result.
- **The per-action witness verdict is deferred.** QL004 reports witness
  presence and dead witnesses from trace counts. Whether each major
  action has a witness is not decided structurally, and the sampled
  coverage row is an advisory.
- **Composition blind spot.** QL003 and QL007 census assignment
  statements in the analysed action's own body, so an assignment made by
  a helper action it calls is invisible. QL008 is not limited this way:
  it follows calls to module actions recursively. QL009 is a
  reachability closure over those calls.
- **Thinness credit is bounded.** A wrapper calling an action whose body
  is a conditional over all branches, rather than a top-level `all`/`any`
  composition, is not credited. The follow is one level: the callee's
  body is inspected, never its callees.
- **Proxy checks are warn-only and say so.** QL002, QL003 and the
  bound-check half of QL006 are mechanical proxies. The report line
  states the proxy.
- **Module-local resolution.** A reference that resolves through an
  import is outside the model. Cross-module analysis is out of scope.
- **Non-ASCII input is refused.** The correction layer is a named
  non-goal until it is designed.
- **The quint contract is structural.** A quint upgrade that keeps the
  consumed fields passes. A semantic change that keeps the fields is
  invisible; the pin and the corpus bound this, they do not remove it.
- **IR table consistency is outside the input contract.** The decoder
  validates every consumed field and cross-checks those fields against
  the source map. It does not cross-check the IR's `table` entry against
  node kinds. A doctored IR with a retargeted table entry is outside the
  input contract (quint 0.33.1 parse output only) and can misattribute a
  QP002 variable or hide a QL006 finding.

## Verification

- **A 143-test suite** (`dune test`): fixture pairs for every check
  (a violating fixture and a clean fixture), decoder refusal cells for
  every schema class the decoder models and every class it refuses,
  plus exit-code fixtures for 0, 1 and 2.
- **A 67-spec corpus of real Quint files**: 47 first-party, 18
  third-party (ChonkyBFT, cosmwasm-to-quint and quint's own examples)
  and 2 synthetic. Every entry typechecks and parses under the pinned
  quint. Corpus entries are never edited to reduce findings, so the
  counters stay comparable across releases. The corpus doubles as the
  decoder drift detector.
- **Every check premise is verified against the quint 0.33.1 source.**
  QP003's premise does not hold (the parser toposorts declarations), so
  the check is not emitted.
- **The spec-to-cell mirror is regression-checked.** The map in
  [`docs/spec-cell-map.jdn`](docs/spec-cell-map.jdn) covers every `i_*`
  invariant in the three specs, and the `sync` test group fails when a
  row, an invariant or a cell name drifts.

## quint-audit specs itself

The verification core of this tool is written in Quint, spec-first: the
OCaml code was written against these specs, not the other way round.
They live in [`spec/`](spec/):

- `qcalc.qnt` - the QP001 truth-table calculus: soundness and refusal
  invariants for the property classifier.
- `rundisc.qnt` - the three-state run discipline: which observable facts
  of a quint invocation may produce a lint verdict, and which may not.
- `irdecode.qnt` - the typed-decode contract: span and source
  attribution rules, declaration kinds and the reporting set.

Each spec is typechecked, run-tested and bounded-model-checked under
quint 0.33.1. Each carries planted mutants, and a mutant counts as
killed only when both instruments fail: a violated invariant under
`quint run` and a failing spec run under `quint test`. The full record
is in [`spec/README.md`](spec/README.md).

The repo's own specs are audited too. `qcalc.qnt` and `rundisc.qnt`
are corpus entries. A release is gated on a clean lint of `spec/`
under the released binary, recorded with the release.

Unit scope: findings name the file that owns them and appear once, even
when one definition is reached through more than one import path. QL009
asks its runnable-unit question of the modules the named file defines,
so a module reached solely through an import gets a `skipped`
step-reachability row, not a pass; linting that module directly keeps
its warn.

## Licence

AGPLv3. The full licence text is in [`LICENSE`](LICENSE), taken from
gnu.org and byte-verified.

The AGPL licence governs the linter's own code only. Findings it
produces and the specs it analyses are not derivative works of the
linter and are unaffected by its licensing terms - proprietary
codebases and CI pipelines can run `quint-audit` with no obligation
beyond the tool itself. The copyleft obligation falls only on those who
modify and redistribute the linter (or serve a modified version), which
is the contribution-back mechanism by design.

## Credits

- [Quint](https://github.com/quint-co/quint) by Informal Systems: the
  language, the parser IR this tool decodes and the runtime that drives
  the `full` checks. Apache-2.0.
- The [Quint LLM kit](https://github.com/quint-co/quint-llm-kit)
  `quint-modeling` review checklist: the baseline of this tool's check
  catalogue and the report row names. Apache-2.0. quint-audit adopts the
  published checklist's row labels and review ideas; no kit code is
  included. The kit is Apache-2.0, which permits this use; quint-audit
  itself is AGPLv3 and is an independent implementation.
- The production-pitfall checks (QP001, QP002) come from recorded
  pitfalls hit while building and verifying Quint models in production.

## AI assistance

The code in this repository was written with the assistance of a large language model and reviewed by its maintainer.
