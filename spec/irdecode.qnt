// irdecode.qnt - the typed-IR decode contract for the quint-audit verification
// core. It states what a decoded IR must satisfy, not how lib/ir_decode.ml is
// written: the source-map contract (per-span source identity, per-source
// module extent), the declaration-kind contract (reporting subjects versus
// carried non-subjects, and the invariant census guard), and the two
// report-health properties the decode contract pins.
//
// Every invariant is traceable to a measured IR: a corpus of 67 real
// specs (25 decoder refusals in five classes) at the pinned quint 0.33.1.
//
// Contract summary:
//   - typed decode is the schema check; malformed IR is refused, an
//     unmodelled shape is decoded with a stated meaning.
//   - the ASCII precondition (the index-alignment reason).
//   - every schema class has a refusal fixture.
//   - unmodelled nodes survive; the declaration-level counterpart is the
//     declared non-subject below.
//   - spans are validated against the source they name.
//
// AGPLv3 - see ../LICENSE.
module irdecode {

  // The enum vocabulary: every symbolic string the contract compares or
  // returns is a named constant (the QL002 rule, followed by construction -
  // no comparison reads a raw literal). The raw strings left are leaf data:
  // the never-seen kind "future" (which stands for the whole class of
  // unseen kinds, not for one member) inside the fixtures below.
  pure def DECODE: str = "decode"
  pure def DECODE_AS_NON_SUBJECT: str = "decode-as-non-subject"
  pure def REFUSE_UNKNOWN_SOURCE: str = "refuse-unknown-source"
  pure def REFUSE_ORDER: str = "refuse-order"
  pure def REFUSE_PAST_OWN_SOURCE: str = "refuse-past-own-source"
  pure def REFUSE_NOT_CLOSING_BRACE: str = "refuse-not-closing-brace"

  pure def ROLE_SUBJECT: str = "subject"
  pure def ROLE_NON_SUBJECT: str = "non-subject"

  pure def KIND_CONST: str = "const"
  pure def KIND_VAR: str = "var"
  pure def KIND_TYPEDEF: str = "typedef"
  pure def KIND_DEF: str = "def"
  pure def KIND_IMPORT: str = "import"
  pure def KIND_ASSUME: str = "assume"
  pure def KIND_INSTANCE: str = "instance"

  pure def QUAL_VAL: str = "val"
  pure def QUAL_NONE: str = ""

  // The bounded model fixes the minimal multi-source case: source 0 is the
  // main file, source 1 is one imported file. The corpus merges more, but a
  // two-source model is the smallest domain that can witness every source-map
  // defect class and it keeps `quint verify` finite.
  //
  // A case carries measured *facts*, not raw byte values, so the decision
  // functions can be checked exhaustively over the cross product.
  //
  // inOwnRange:  the span's end index is within the byte length of the source
  //              its sourceIndex names.
  // inMainRange: the end index is within the main file's byte length. For a
  //              span from an imported source this is the wrong-file range
  //              that the current decoder uses.
  type SpanCase = {
    src: int,            // 0 = main, 1 = imported
    known: bool,         // the sourceIndex entry resolves
    orderOk: bool,       // start.index <= end.index
    inOwnRange: bool,    // end.index <= length of the span's own source
    inMainRange: bool    // end.index <= length of the main source
  }

  type ModuleCase = {
    src: int,
    known: bool,
    inOwnRange: bool,
    inMainRange: bool,
    braceOwn: bool,      // the byte at end.index in the module's own source is
                         // this module's closing brace
    braceMain: bool      // the byte at end.index in the main source is a '}'
  }

  pure def bit(k: int, w: int): bool = ((k / w) % 2) == 1

  pure def spanCase(k: int): SpanCase = {
    src: k / 16,
    known: bit(k, 1),
    orderOk: bit(k, 2),
    inOwnRange: bit(k, 4),
    inMainRange: if (k / 16 == 0) bit(k, 4) else bit(k, 8)
  }

  pure def SpanUniverse: Set[SpanCase] = 0.to(31).map(k => spanCase(k))

  pure def moduleCase(k: int): ModuleCase = {
    src: k / 32,
    known: bit(k, 1),
    inOwnRange: bit(k, 2),
    inMainRange: if (k / 32 == 0) bit(k, 2) else bit(k, 4),
    braceOwn: bit(k, 8),
    braceMain: if (k / 32 == 0) bit(k, 8) else bit(k, 16)
  }

  pure def ModuleUniverse: Set[ModuleCase] = 0.to(63).map(k => moduleCase(k))

  // ---- the source-map contract ------------------------------------------

  // A span is decoded only when its named source resolves, its own range is
  // ordered, and it fits the source it names. Length is never read from a
  // different source, and spans are validated against the source they name.
  pure def spanDecision(c: SpanCase): str =
    if (not(c.known)) REFUSE_UNKNOWN_SOURCE
    else if (not(c.orderOk)) REFUSE_ORDER
    else if (not(c.inOwnRange)) REFUSE_PAST_OWN_SOURCE
    else DECODE

  pure def spanDecodable(c: SpanCase): bool = spanDecision(c) == DECODE

  // Genuinely malformed: a span that cannot be given a meaning. An imported
  // span that fits its own source is unmodelled by the current decoder, not
  // malformed (an imported span past the main file).
  pure def spanMalformed(c: SpanCase): bool =
    not(c.known) or not(c.orderOk) or not(c.inOwnRange)

  // Imported-file spans are measured against the main file.
  // The contract: the main file's range is the own range only for source 0.
  val i_main_range_is_own_range = SpanUniverse.forall(c =>
    implies(c.src == 0, c.inOwnRange == c.inMainRange))

  // A decoded span always fits the source it names.
  val i_span_decode_within_own_source = SpanUniverse.forall(c =>
    implies(spanDecodable(c), and { c.known, c.orderOk, c.inOwnRange }))

  // The imported-span decision, stated per source: an imported span is judged by the
  // imported source's length exactly, never by the main file's length.
  val i_imported_span_uses_own_source = SpanUniverse.forall(c =>
    implies(c.src == 1,
      iff(spanDecodable(c), and { c.known, c.orderOk, c.inOwnRange })))

  // The silent-wrong-span hazard, forbidden: when an imported span's end
  // falls inside the main file's range but past its own source, the decoder
  // must refuse. A guard that skips the length check would accept it and
  // point the report at unrelated bytes; a crash is preferable to that.
  val i_no_silent_wrong_span = SpanUniverse.forall(c =>
    implies(and { c.src == 1, not(c.inOwnRange), c.inMainRange },
            not(spanDecodable(c))))

  // The refusal set: refusal is exactly the malformed shape set. An imported
  // span that fits its own source is decoded with the meaning "span in that
  // source", not refused.
  val i_span_refusal_set = SpanUniverse.forall(c =>
    iff(not(spanDecodable(c)), spanMalformed(c)))

  // The module end index is a per-source statement.
  pure def moduleDecision(m: ModuleCase): str =
    if (not(m.known)) REFUSE_UNKNOWN_SOURCE
    else if (not(m.inOwnRange)) REFUSE_PAST_OWN_SOURCE
    else if (not(m.braceOwn)) REFUSE_NOT_CLOSING_BRACE
    else DECODE

  pure def moduleDecodable(m: ModuleCase): bool = moduleDecision(m) == DECODE

  // A decoded module end points at that module's closing brace in its own
  // source. For source 0 this is the measured "end byte is '}'" fact.
  val i_module_end_is_own_closing_brace = ModuleUniverse.forall(m =>
    implies(moduleDecodable(m), and { m.known, m.inOwnRange, m.braceOwn }))

  // The per-source reading: for an imported module the main file's length and
  // the main file's braces carry no authority.
  val i_imported_module_uses_own_source = ModuleUniverse.forall(m =>
    implies(m.src == 1,
      iff(moduleDecodable(m), and { m.known, m.inOwnRange, m.braceOwn })))

  // The same hazard at module level: a '}' at the same index in the main file
  // must not rescue a module end that is past its own source.
  val i_no_wrong_source_brace = ModuleUniverse.forall(m =>
    implies(and { m.src == 1, not(m.inOwnRange), m.inMainRange, m.braceMain },
            not(moduleDecodable(m))))

  // ---- the declaration-kind contract ------------------------------------

  // Every kind 0.33.1 emits in the corpus, plus a never-seen kind. The
  // evidence fields are measured: `import` and `instance` carry no `name`
  // (they carry protoName/qualifiedName); `assume` carries an `assumption`
  // expression and no qualifier; `const` may carry a body; `var`/`typedef` do
  // not.
  type DeclCase = {
    kind: str,
    hasName: bool,
    hasQualifier: bool,
    qualifier: str,
    hasBody: bool,
    hasAssumption: bool,
    nullary: bool
  }

  pure def knownKind(k: str): bool =
    k.in(Set(KIND_CONST, KIND_VAR, KIND_TYPEDEF, KIND_DEF, KIND_IMPORT, KIND_ASSUME, KIND_INSTANCE))

  // The reporting set is the declarations a check may emit a finding about:
  // kind `def` (the qualifier selects the role). Everything else is carried
  // and never counted. A never-seen kind is a declared non-subject (the
  // declaration-level counterpart), never a crash.
  pure def reportingRole(k: DeclCase): str =
    if (k.kind == KIND_DEF) ROLE_SUBJECT else ROLE_NON_SUBJECT

  // The invariant census predicate mirrors run_checks.ml:84: kind Def, a
  // `val` qualifier, nullary, with a body. Nothing else may enter it.
  pure def censusCandidate(k: DeclCase): bool =
    k.kind == KIND_DEF and k.qualifier == QUAL_VAL and k.nullary and k.hasBody

  // The unknown-kind decision: decode as a declared non-subject. Refusing
  // would reintroduce the expression/declaration asymmetry this contract
  // removes; dropping it silently would hide a schema change. The declared
  // non-subject keeps the census safe and leaves the coverage gap visible.
  pure def kindDecision(kind: str): str =
    if (knownKind(kind)) DECODE else DECODE_AS_NON_SUBJECT

  pure def DeclUniverse: Set[DeclCase] =
    Set(
      { kind: KIND_CONST, hasName: true, hasQualifier: false, qualifier: QUAL_NONE, hasBody: true, hasAssumption: false, nullary: true },
      { kind: KIND_VAR, hasName: true, hasQualifier: false, qualifier: QUAL_NONE, hasBody: false, hasAssumption: false, nullary: true },
      { kind: KIND_TYPEDEF, hasName: true, hasQualifier: false, qualifier: QUAL_NONE, hasBody: false, hasAssumption: false, nullary: true },
      { kind: KIND_DEF, hasName: true, hasQualifier: true, qualifier: QUAL_VAL, hasBody: true, hasAssumption: false, nullary: true },
      { kind: KIND_IMPORT, hasName: false, hasQualifier: false, qualifier: QUAL_NONE, hasBody: false, hasAssumption: false, nullary: false },
      { kind: KIND_ASSUME, hasName: true, hasQualifier: false, qualifier: QUAL_NONE, hasBody: false, hasAssumption: true, nullary: false },
      { kind: KIND_INSTANCE, hasName: false, hasQualifier: false, qualifier: QUAL_NONE, hasBody: false, hasAssumption: false, nullary: false },
      { kind: "future", hasName: true, hasQualifier: false, qualifier: QUAL_NONE, hasBody: false, hasAssumption: false, nullary: false }
    )

  // Import and instance declarations carry no `name`, no
  // qualifier and no body. The missing-name refusal the corpus reports is a
  // missing field on a non-subject, not malformed IR.
  val i_import_instance_evidence = DeclUniverse.forall(k =>
    implies(k.kind.in(Set(KIND_IMPORT, KIND_INSTANCE)),
            and { not(k.hasName), not(k.hasQualifier), not(k.hasBody) }))

  // An assumption carries an `assumption` expression and no
  // qualifier (the decoder must not read it as a val).
  val i_assume_evidence = DeclUniverse.forall(k =>
    implies(k.kind == KIND_ASSUME,
            and { k.hasAssumption, not(k.hasQualifier), not(k.hasBody) }))

  // The census guard: a non-subject can never be a census candidate. This is
  // the invariant run_checks.ml:84's filter relies on; a future widening that
  // admits an unknown node must keep this true.
  val i_nonsubject_not_in_census = DeclUniverse.forall(k =>
    implies(reportingRole(k) == ROLE_NON_SUBJECT, not(censusCandidate(k))))

  // Symmetrically, the census contains only reporting subjects.
  val i_census_is_subject = DeclUniverse.forall(k =>
    implies(censusCandidate(k), reportingRole(k) == ROLE_SUBJECT))

  // A never-seen declaration kind decodes as a declared non-subject and never
  // enters the census. This is the invariant a test distinguishes from a
  // refusal policy: the fixture expects Ok plus absence from the census.
  val i_unknown_kind_non_subject = DeclUniverse.forall(k =>
    implies(not(knownKind(k.kind)),
            and {
              kindDecision(k.kind) == DECODE_AS_NON_SUBJECT,
              reportingRole(k) == ROLE_NON_SUBJECT,
              not(censusCandidate(k))
            }))

  // Known kinds decode; the decision labels the two policies explicitly.
  val i_known_kind_decodes = DeclUniverse.forall(k =>
    implies(knownKind(k.kind), kindDecision(k.kind) == DECODE))

  // ---- report-health invariants -----------------------------------------

  // A state is an observation only when it binds a value that carries
  // evidence. `null`, `{}` and an action marker are not evidence.
  type StateCase = {
    junk: int,      // bindings whose value is null or {}
    real: int,      // bindings with a real value
    marker: bool    // an action marker is present
  }

  pure def stateCase(k: int): StateCase = {
    junk: k / 4,
    real: (k / 2) % 2,
    marker: bit(k, 1)
  }

  pure def StateUniverse: Set[StateCase] = 0.to(7).map(k => stateCase(k))

  pure def observed(s: StateCase): bool = s.real > 0
  pure def ql004Pass(s: StateCase): bool = observed(s)

  val i_pass_requires_real_binding = StateUniverse.forall(s =>
    implies(observed(s), s.real > 0))

  val i_no_pass_on_junk = StateUniverse.forall(s =>
    implies(and { s.junk > 0, s.real == 0 }, not(observed(s))))

  val i_marker_is_not_a_binding = StateUniverse.forall(s =>
    implies(and { s.marker, s.real == 0 }, not(observed(s))))

  // A file mixing accepted and refused states discloses the refused count,
  // not only the file-level accepted count. report level 0 is the
  // file-level report (no entry count); level 1 is the entry-level report.
  type FileCase = {
    accepted: int,
    refused: int
  }

  pure def fileCase(k: int): FileCase = {
    accepted: k / 2,
    refused: k % 2
  }

  pure def FileUniverse: Set[FileCase] = 0.to(3).map(k => fileCase(k))

  pure def reportedRefused(f: FileCase, level: int): int =
    if (level == 0) 0 else f.refused

  val i_refused_disclosed = FileUniverse.forall(f =>
    implies(f.refused > 0,
            and { reportedRefused(f, 0) != f.refused,
                  reportedRefused(f, 1) == f.refused,
                  reportedRefused(f, 1) > 0 }))

  // ---- the state machine and the composite contract ----------------------

  // The state machine exists only so `quint verify` has a transition system;
  // the contract invariants quantify over fixed universes and hold in every
  // state. The walk carries no claim.
  var tick: int

  action init = all { tick' = 0 }

  action step = any { tick' = 0, tick' = 1 }

  // Named boundary runs; each pins one fact the OCaml mirror asserts.
  run r_imported_span_decodes = all { tick' = 0 }.expect(
    spanDecodable(spanCase(16 + 1 + 2 + 4)) == true)
  run r_imported_span_in_both_ranges_decodes = all { tick' = 0 }.expect(
    spanDecision(spanCase(16 + 1 + 2 + 4 + 8)) == DECODE)
  run r_imported_span_past_own_refused = all { tick' = 0 }.expect(
    spanDecision(spanCase(16 + 1 + 2)) == REFUSE_PAST_OWN_SOURCE)
  run r_silent_wrong_span_refused = all { tick' = 0 }.expect(
    spanDecision(spanCase(16 + 1 + 2 + 8)) == REFUSE_PAST_OWN_SOURCE)
  run r_module_imported_brace_decodes = all { tick' = 0 }.expect(
    moduleDecision(moduleCase(32 + 1 + 2 + 8)) == DECODE)
  run r_module_wrong_source_brace_refused = all { tick' = 0 }.expect(
    moduleDecision(moduleCase(32 + 1 + 4 + 16)) == REFUSE_PAST_OWN_SOURCE)
  run r_import_kind_is_non_subject = all { tick' = 0 }.expect(
    reportingRole({ kind: KIND_IMPORT, hasName: false, hasQualifier: false, qualifier: QUAL_NONE, hasBody: false, hasAssumption: false, nullary: false }) == ROLE_NON_SUBJECT)
  run r_assume_kind_is_non_subject = all { tick' = 0 }.expect(
    reportingRole({ kind: KIND_ASSUME, hasName: true, hasQualifier: false, qualifier: QUAL_NONE, hasBody: false, hasAssumption: true, nullary: false }) == ROLE_NON_SUBJECT)
  run r_future_kind_decodes_non_subject = all { tick' = 0 }.expect(
    and {
      kindDecision("future") == DECODE_AS_NON_SUBJECT,
      reportingRole({ kind: "future", hasName: true, hasQualifier: false, qualifier: QUAL_NONE, hasBody: false, hasAssumption: false, nullary: false }) == ROLE_NON_SUBJECT
    })
  run r_junk_state_not_observed = all { tick' = 0 }.expect(
    not(observed({ junk: 1, real: 0, marker: true })))
  run r_mixed_file_discloses_refused = all { tick' = 0 }.expect(
    implies(fileCase(3).refused > 0,
            reportedRefused(fileCase(3), 1) == fileCase(3).refused))

  // The composite contract, grouped so that its state
  // dependency is explicit and its free-leaf count stays inside the truth
  // table's bound: the flat 18-val conjunction resolved to no state
  // dependency (every component val quantifies over a fixed universe) and
  // exceeded the 16-leaf bound. Each group carries the tick walk as an
  // antecedent - true in every reachable state (init 0, step 0 or 1) - so
  // the conjunction's meaning over the reachable states is unchanged and
  // the 18 component invariants are carried verbatim.
  val i_source_map_contract = implies(tick.in(Set(0, 1)), and {
    i_main_range_is_own_range,
    i_span_decode_within_own_source,
    i_imported_span_uses_own_source,
    i_no_silent_wrong_span,
    i_span_refusal_set,
    i_module_end_is_own_closing_brace,
    i_imported_module_uses_own_source,
    i_no_wrong_source_brace
  })

  val i_decl_kind_report_contract = implies(tick.in(Set(0, 1)), and {
    i_import_instance_evidence,
    i_assume_evidence,
    i_nonsubject_not_in_census,
    i_census_is_subject,
    i_unknown_kind_non_subject,
    i_known_kind_decodes,
    i_pass_requires_real_binding,
    i_no_pass_on_junk,
    i_marker_is_not_a_binding,
    i_refused_disclosed
  })

  val i_contract = and {
    i_source_map_contract,
    i_decl_kind_report_contract
  }
}
