# Semantic kernel hardening — phase 1

## Purpose

The existing PCC-K implementation checks proof-node shape, rule names, premise ordering, digests, modes, and selected safety properties. Those checks are necessary, but they do not by themselves establish that a node's conclusion follows from its premises under the named primitive rule.

This phase begins replacing assertion-shaped proof records with a fail-closed semantic proof kernel.

## Delivered in this phase

`pcc-kernel-semantic0.mjs` implements a typed term language and semantic checking for the primitive `Eq` family:

- reflexivity: `t = t`;
- symmetry: from `a = b`, infer `b = a`;
- transitivity: from `a = b` and `b = c`, infer `a = c`;
- application congruence: argument equalities justify equality of applications with the same symbol, result sort, and arity.

The checker also enforces:

- well-sorted equality judgments;
- unique proof-node identifiers;
- earlier-premise-only DAG discipline;
- canonical digests over checked data;
- explicit operation tags;
- full-mode-only checking in phase 1;
- deterministic first-failure coordinates;
- rejection of every primitive rule without an implemented semantic handler.

`CheckSemanticKernelReadiness0` is a machine-checkable release blocker. It derives coverage from the handlers implemented in the module; callers cannot override the supported-rule set with metadata. The gate remains rejected until every currently declared primitive rule has executable semantics.

## Current status

Implemented semantic rule family:

```text
Eq
```

Still required:

```text
Subst
Record
DAGInd
LedgerInd
OblTopoInd
TraceInd
FiniteExhaust
DPInd
Hall
RankInd
MinCounterexample
IntArith
Transport
TruthVec
FiniteRel
```

Accordingly, this phase does **not** make the final `P = NP` theorem ready for emission. It creates the first semantic rule implementation and a fail-closed gate that prevents this partial kernel from being represented as complete.

## Verification

Run:

```bash
node --check pcc-kernel-semantic0.mjs
node --test test/pcc-kernel-semantic0.test.mjs
```

The tests cover accepted reflexivity, symmetry, transitivity, and congruence, plus rejection of arbitrary labelled equalities, invalid transitivity, forward premises, unsupported rules, sort mismatches, and mutated congruence conclusions. They also require the readiness gate to remain closed while semantic rule coverage is incomplete.

## Required follow-on sequence

1. Implement `Subst` with capture-avoiding typed substitution and exact premise/conclusion matching.
2. Implement `Record` as an explicit judgment constructor rather than a free-form payload.
3. Implement the finite computational rules (`TruthVec`, `FiniteRel`, `IntArith`) against independently specified evaluators.
4. Implement induction and combinatorial rules with explicit invariants, base cases, steps, and finite domains.
5. Re-encode V53 and V54 as derivations accepted by the semantic kernel rather than registry entries whose theorem names and conclusions are merely present.
6. Replace checker-reflection assertions with proof-producing refinement checks that connect accepted records to precise public judgments.
7. Wire `CheckSemanticKernelReadiness0` and semantic proof checking into `CheckKImpl0`, the global proof DAG, package sufficiency, and the final release gate.
8. Migrate every claim-critical proof node and add mutation tests that alter a premise, side condition, or conclusion and require rejection.
9. Publish the completed work as a new source/checker and artefact release; do not rewrite the sealed `7072f8d` release.

## Completion criterion

The semantic-kernel gap is closed only when:

- all primitive rules used by the final DAG have implemented semantics;
- every final-DAG node is checked under those semantics;
- Sigma theorems are checked derivations;
- reflection mappings prove the advertised checker judgments;
- the readiness gate accepts;
- mutation and independent review find no missing logical implication;
- a new immutable release records the new checker and artefact identities.
