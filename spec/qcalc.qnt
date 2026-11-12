// qcalc.qnt - the QP001 classification calculus for the quint-audit
// verification core: the truth-table calculus that decides whether a
// boolean property body is a constant. The contract is stated in
// ./README.md. AGPLv3 - see ../LICENSE.
module qcalc {

  // A boolean body is a fixed-depth tree: a Body node applies an operator
  // to two Node1s; a Node1 applies an operator to two atoms; "wrap" lifts a
  // single atom to a node (its right child is an ignored dummy literal).
  // The spec is about the classification function's contract, not parsing.
  type Atom = { kind: str, lit: bool, name: str }
  type Node1 = { op: str, l: Atom, r: Atom }
  type Body = { op: str, l: Node1, r: Node1 }

  // The enum vocabulary: every symbolic string the contract compares or
  // returns is a named constant (the QL002 rule, followed by construction -
  // no comparison reads a raw literal). The only raw strings left are leaf
  // data: variable names and LeafKey tags, which are never compared.
  pure def K_LIT: str = "lit"
  pure def K_VAR: str = "var"
  pure def K_SPINE: str = "spine"

  pure def OP_WRAP: str = "wrap"
  pure def OP_AND: str = "and"
  pure def OP_OR: str = "or"
  pure def OP_NOT: str = "not"
  pure def OP_IMPLIES: str = "implies"
  pure def OP_IFF: str = "iff"
  pure def OP_EQ: str = "eq"
  pure def OP_NEQ: str = "neq"

  pure def CLASS_CONST_TRUE: str = "const-true"
  pure def CLASS_CONST_FALSE: str = "const-false"
  pure def CLASS_VARIES: str = "varies"
  pure def CLASS_UNKNOWN: str = "unknown"

  pure def DECISION_PASS: str = "pass"
  pure def DECISION_REFUSE: str = "refuse"

  // atoms: "lit" carries its value in lit; "var" is a leaf named name;
  // "spine" marks an unmodelled expression spine - the refusal marker.
  pure def LIT(v: bool): Atom = { kind: K_LIT, lit: v, name: "" }
  pure def VAR(n: str): Atom = { kind: K_VAR, lit: false, name: n }
  pure def SPINE: Atom = { kind: K_SPINE, lit: false, name: "" }

  pure def w1(a: Atom): Node1 = { op: OP_WRAP, l: a, r: LIT(false) }
  pure def n1(op: str, l: Atom, r: Atom): Node1 = { op: op, l: l, r: r }
  pure def n2(op: str, l: Node1, r: Node1): Body = { op: op, l: l, r: r }

  // the connective semantics, uniform over both node levels
  pure def applyOp(op: str, l: bool, r: bool): bool =
    if (op == OP_WRAP) l
    else if (op == OP_AND) l and r
    else if (op == OP_OR) l or r
    else if (op == OP_NOT) not(l)
    else if (op == OP_IMPLIES) l implies r
    else if (op == OP_IFF) l iff r
    else if (op == OP_EQ) l == r
    else if (op == OP_NEQ) l != r
    else false

  // The contract's modelled operator list (QP001).
  // Fixed: the invariants are stated against this set and no mutant edits it.
  pure def ContractOps: Set[str] = Set(OP_AND, OP_OR, OP_NOT, OP_IMPLIES, OP_IFF, OP_EQ, OP_NEQ, OP_WRAP)

  // The classifier's recognition set. Equal to the contract list; the
  // spec-level mutants edit this def (mutant m-a drops OP_IMPLIES).
  pure def RecognisedOps: Set[str] = Set(OP_AND, OP_OR, OP_NOT, OP_IMPLIES, OP_IFF, OP_EQ, OP_NEQ, OP_WRAP)

  // refusal: a spine atom anywhere, or an operator outside the recognition
  // set, makes the body unclassifiable
  pure def atomSpine(a: Atom): bool = a.kind == K_SPINE

  pure def n1Spine(n: Node1): bool = atomSpine(n.l) or atomSpine(n.r)

  pure def bodySpine(b: Body): bool = n1Spine(b.l) or n1Spine(b.r)

  pure def n1Refuses(n: Node1): bool =
    (not(n.op.in(RecognisedOps))) or atomSpine(n.l) or atomSpine(n.r)

  pure def bodyRefuses(b: Body): bool =
    (not(b.op.in(RecognisedOps))) or n1Refuses(b.l) or n1Refuses(b.r)

  // contract-side modelled-spine check, the antecedent of I-EXHAUSTIVE and
  // I-EQ-IDENTITY: built only from ContractOps and the spine markers, never
  // from the classifier's recognition set
  pure def n1Modelled(n: Node1): bool =
    n.op.in(ContractOps) and not(atomSpine(n.l)) and not(atomSpine(n.r))

  pure def spineModelled(b: Body): bool =
    b.op.in(ContractOps) and n1Modelled(b.l) and n1Modelled(b.r)

  // Free leaves of the truth table: every distinct var atom, plus
  // every eq/neq node whose subtrees are not canonically identical, as an
  // opaque leaf. Leaf identity is structural: two occurrences of the same
  // subtree share one leaf (they carry the same value); distinct subtrees
  // get distinct leaves. eq/neq with identical subtrees contributes its
  // constant (true/false), not a leaf.
  type LeafKey = { tag: str, name: str, sub1: Node1, sub2: Body }

  // dummy fillers so every LeafKey has the full record shape
  pure def DUMMY1: Node1 = { op: OP_WRAP, l: LIT(false), r: LIT(false) }
  pure def DUMMY2: Body = { op: OP_WRAP, l: DUMMY1, r: DUMMY1 }

  pure def keyVar(n: str): LeafKey = { tag: "v", name: n, sub1: DUMMY1, sub2: DUMMY2 }
  pure def keyEqN1(n: Node1): LeafKey = { tag: "e1", name: "", sub1: n, sub2: DUMMY2 }
  pure def keyEqB(b: Body): LeafKey = { tag: "e2", name: "", sub1: DUMMY1, sub2: b }

  pure def leafAtom(a: Atom): Set[LeafKey] =
    if (a.kind == K_VAR) Set(keyVar(a.name)) else Set()

  pure def leavesN1(n: Node1): Set[LeafKey] =
    if (n.op == OP_WRAP) leafAtom(n.l)
    else if (n.op == OP_EQ or n.op == OP_NEQ)
      (if (n.l == n.r) Set() else Set(keyEqN1(n)))
    else leafAtom(n.l).union(leafAtom(n.r))

  pure def leavesBody(b: Body): Set[LeafKey] =
    if (b.op == OP_WRAP) leavesN1(b.l)
    else if (b.op == OP_EQ or b.op == OP_NEQ)
      (if (b.l == b.r) Set() else Set(keyEqB(b)))
    else leavesN1(b.l).union(leavesN1(b.r))

  // concrete evaluation: the definitional ground truth. An assignment is the
  // set of free leaves assigned true; eq/neq compares the concrete values
  // of its two subtrees.
  pure def evalAtom(a: Atom, asg: Set[LeafKey]): bool =
    if (a.kind == K_LIT) a.lit
    else if (a.kind == K_VAR) keyVar(a.name).in(asg)
    else false

  pure def evalN1(n: Node1, asg: Set[LeafKey]): bool =
    applyOp(n.op, evalAtom(n.l, asg), evalAtom(n.r, asg))

  pure def evalBody(b: Body, asg: Set[LeafKey]): bool =
    applyOp(b.op, evalN1(b.l, asg), evalN1(b.r, asg))

  // every var leaf appearing anywhere in the body (concrete eval reads
  // them, including inside eq children)
  pure def varKeysAtom(a: Atom): Set[LeafKey] =
    if (a.kind == K_VAR) Set(keyVar(a.name)) else Set()

  pure def varKeysN1(n: Node1): Set[LeafKey] =
    varKeysAtom(n.l).union(varKeysAtom(n.r))

  pure def varKeysBody(b: Body): Set[LeafKey] =
    varKeysN1(b.l).union(varKeysN1(b.r))

  // table evaluation: how the classifier values a body while enumerating
  // assignments over its free leaves. A var atom reads its leaf; an eq/neq
  // with identical subtrees contributes its constant; an eq/neq with
  // distinct subtrees reads its opaque free leaf.
  pure def tabAtom(a: Atom, asg: Set[LeafKey]): bool =
    if (a.kind == K_LIT) a.lit
    else if (a.kind == K_VAR) keyVar(a.name).in(asg)
    else false

  pure def tabN1(n: Node1, asg: Set[LeafKey]): bool =
    if (n.op == OP_EQ or n.op == OP_NEQ)
      (if (n.l == n.r) (n.op == OP_EQ) else keyEqN1(n).in(asg))
    else applyOp(n.op, tabAtom(n.l, asg), tabAtom(n.r, asg))

  pure def tabBody(b: Body, asg: Set[LeafKey]): bool =
    if (b.op == OP_EQ or b.op == OP_NEQ)
      (if (b.l == b.r) (b.op == OP_EQ) else keyEqB(b).in(asg))
    else applyOp(b.op, tabN1(b.l, asg), tabN1(b.r, asg))

  // assignment enumeration over the free leaves (all subsets), built by
  // fold: 0.33 forbids recursive defs (QNT099) and has no set flatMap
  pure def extendSubsets(acc: Set[Set[LeafKey]], e: LeafKey): Set[Set[LeafKey]] =
    acc.union(acc.map(t => t.union(Set(e))))

  pure def allSubsets(s: Set[LeafKey]): Set[Set[LeafKey]] =
    s.fold(Set(Set()), (acc, e) => extendSubsets(acc, e))

  // the classifier (QP001's truth table): unknown on refusal; otherwise
  // evaluate the table over every assignment of the free leaves
  pure def classify(b: Body): str =
    if (bodyRefuses(b)) CLASS_UNKNOWN
    else {
      val rs = allSubsets(leavesBody(b)).map(a => tabBody(b, a))
      if (rs.forall(x => x)) CLASS_CONST_TRUE
      else if (rs.forall(x => not(x))) CLASS_CONST_FALSE
      else CLASS_VARIES
    }

  // downstream decision: only a varying body passes; every constant and every
  // refusal is a QP001 finding (the refusal/pass discipline)
  pure def decision(b: Body): str =
    if (classify(b) == CLASS_VARIES) DECISION_PASS else DECISION_REFUSE

  // the bounded verification domain: a representative pool of bodies
  // covering every contract shape (tautologies, contradictions, varying
  // bodies, eq identities and non-identities, spines, wraps)
  pure def NOT1(a: Atom): Node1 = n1(OP_NOT, a, LIT(false))

  pure def b_implies_taut: Body = n2(OP_IMPLIES, w1(VAR("x")), w1(VAR("x")))
  pure def b_and_not: Body = n2(OP_AND, w1(VAR("x")), NOT1(VAR("x")))
  pure def b_or_not: Body = n2(OP_OR, w1(VAR("x")), NOT1(VAR("x")))
  pure def b_or_true: Body = n2(OP_OR, w1(LIT(true)), w1(VAR("x")))
  pure def b_and_false: Body = n2(OP_AND, w1(LIT(false)), w1(VAR("x")))
  pure def b_implies_lits: Body = n2(OP_IMPLIES, w1(LIT(true)), w1(LIT(false)))
  pure def b_iff_not: Body = n2(OP_IFF, w1(VAR("x")), NOT1(VAR("x")))
  pure def b_or_xy: Body = n2(OP_OR, w1(VAR("x")), w1(VAR("y")))
  pure def b_and_xy: Body = n2(OP_AND, w1(VAR("x")), w1(VAR("y")))
  pure def b_eq_ident: Body = n2(OP_EQ, w1(VAR("x")), w1(VAR("x")))
  pure def b_eq_distinct: Body = n2(OP_EQ, w1(VAR("x")), w1(VAR("y")))
  pure def b_eq_nodes_ident: Body =
    n2(OP_EQ, n1(OP_OR, VAR("x"), VAR("y")), n1(OP_OR, VAR("x"), VAR("y")))
  pure def b_eq_nodes_distinct: Body =
    n2(OP_EQ, n1(OP_OR, VAR("x"), VAR("y")), n1(OP_AND, VAR("x"), VAR("y")))
  pure def b_neq_ident: Body = n2(OP_NEQ, w1(VAR("x")), w1(VAR("x")))
  pure def b_spine_and: Body = n2(OP_AND, w1(SPINE), w1(VAR("x")))
  pure def b_spine_eq: Body = n2(OP_EQ, w1(SPINE), w1(SPINE))
  pure def b_implies_nodes: Body =
    n2(OP_IMPLIES, n1(OP_OR, VAR("x"), VAR("y")), n1(OP_OR, VAR("x"), VAR("y")))
  pure def b_wrap_top: Body = n2(OP_WRAP, n1(OP_OR, VAR("x"), VAR("y")), w1(LIT(false)))

  pure def Pool: Set[Body] = Set(
    b_implies_taut,
    b_and_not,
    b_or_not,
    b_or_true,
    b_and_false,
    b_implies_lits,
    b_iff_not,
    b_or_xy,
    b_and_xy,
    b_eq_ident,
    b_eq_distinct,
    b_eq_nodes_ident,
    b_eq_nodes_distinct,
    b_neq_ident,
    b_spine_and,
    b_spine_eq,
    b_implies_nodes,
    b_wrap_top
  )

  // the state machine: walks pool bodies so `quint run` exercises the
  // classifier; the invariants below are pool-quantified and hold at
  // every state regardless of the walk
  var body: Body

  action init = all {
    nondet b = Pool.oneOf()
    body' = b
  }

  action step = any {
    all {
      nondet b = Pool.oneOf()
      body' = b
    }
  }

  // the contract runs: each pins one classification fact the OCaml
  // implementation must mirror; the spec mutants die here (and under
  // `quint run --invariant`, never only one instrument)
  run r_implies_tautology = all { body' = b_implies_taut }.expect(classify(body) == CLASS_CONST_TRUE)
  run r_or_not_tautology = all { body' = b_or_not }.expect(classify(body) == CLASS_CONST_TRUE)
  run r_and_not_contradiction = all { body' = b_and_not }.expect(classify(body) == CLASS_CONST_FALSE)
  run r_iff_not_contradiction = all { body' = b_iff_not }.expect(classify(body) == CLASS_CONST_FALSE)
  run r_or_varies = all { body' = b_or_xy }.expect(classify(body) == CLASS_VARIES)
  run r_wrap_varies = all { body' = b_wrap_top }.expect(classify(body) == CLASS_VARIES)
  run r_eq_identity = all { body' = b_eq_ident }.expect(classify(body) == CLASS_CONST_TRUE)
  run r_eq_node_identity = all { body' = b_eq_nodes_ident }.expect(classify(body) == CLASS_CONST_TRUE)
  run r_eq_distinct_varies = all { body' = b_eq_distinct }.expect(classify(body) == CLASS_VARIES)
  run r_neq_identity_false = all { body' = b_neq_ident }.expect(classify(body) == CLASS_CONST_FALSE)
  run r_spine_unknown = all { body' = b_spine_and }.expect(classify(body) == CLASS_UNKNOWN)
  run r_spine_eq_unknown = all { body' = b_spine_eq }.expect(classify(body) == CLASS_UNKNOWN)
  run r_spine_refused = all { body' = b_spine_and }.expect(decision(body) == DECISION_REFUSE)
  run r_sound_true_all_assignments = all { body' = b_or_not }.expect(
    allSubsets(varKeysBody(body)).forall(a => evalBody(body, a)))
  run r_sound_false_all_assignments = all { body' = b_and_not }.expect(
    allSubsets(varKeysBody(body)).forall(a => not(evalBody(body, a))))

  // the contract invariants (I-*), pool-quantified so every state of every
  // bounded run checks every pool body. Verified bounded via `quint run`;
  // recorded as bounded, never claimed as proofs.

  // I-EXHAUSTIVE: a body whose spine is modelled is classified a constant
  // or varies - never unknown
  val i_exhaustive = Pool.forall(b =>
    implies(spineModelled(b), classify(b).in(Set(CLASS_CONST_TRUE, CLASS_CONST_FALSE, CLASS_VARIES))))

  // I-SOUND-TRUE: const-true means true under every assignment (definition
  // soundness; the table's free leaves over-approximate the concrete ones)
  val i_sound_true = Pool.forall(b =>
    implies(classify(b) == CLASS_CONST_TRUE,
      allSubsets(varKeysBody(b)).forall(a => evalBody(b, a))))

  // I-SOUND-FALSE: const-false means false under every assignment
  val i_sound_false = Pool.forall(b =>
    implies(classify(b) == CLASS_CONST_FALSE,
      allSubsets(varKeysBody(b)).forall(a => not(evalBody(b, a)))))

  // I-REFUSE-UNKNOWN: unknown is a refusal - never a pass (a spine-bearing
  // or unclassifiable body never reaches the pass lane)
  val i_refuse_unknown = Pool.forall(b =>
    implies(or(bodySpine(b), classify(b) == CLASS_UNKNOWN), decision(b) == DECISION_REFUSE))

  // I-EQ-IDENTITY: eq over canonically identical subtrees is const-true;
  // eq over distinct subtrees is varies
  val i_eq_identity = Pool.forall(b =>
    and {
      implies(
        and { b.op == OP_EQ, b.l == b.r, spineModelled(b) },
        classify(b) == CLASS_CONST_TRUE),
      implies(
        and { b.op == OP_EQ, b.l != b.r, spineModelled(b) },
        classify(b) == CLASS_VARIES)
    })
}
