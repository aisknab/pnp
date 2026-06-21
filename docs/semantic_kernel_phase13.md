# Semantic kernel hardening — phase 13 (`FiniteExhaust`)

## Purpose

Phases 1–12 implemented semantic checking for `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, exact finite `LedgerInd`, obligation lifecycle induction, topological NAND `TraceInd`, successor KImpl boundaries, and KBundle/global gates that quarantine every legacy final theorem node.

Phase 13 implements the next primitive PCC-K rule family, `FiniteExhaust`.

The report uses finite exhaustion for bounded tables, finite profile alphabets, finite row universes, and bounded evaluator cases. A semantic exhaustion rule must bind a concrete finite domain, verify that its enumeration is canonical and duplicate-free, require one accepted proof for every enumerated element, and compute the universal result. It must not accept `complete = true`, a claimed cardinality, or a finite-domain label as a replacement for case evidence.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`FiniteExhaust` proves a universal judgment only over the explicit domain stored in the proof object. It does not prove that an arbitrary external mathematical set is represented by that domain.

Any bridge from a package-specific object family to a `SemanticFiniteDomain0` must be checked by the rule that constructs that family. Once a domain is explicit, `FiniteExhaust` verifies exact enumeration and exact per-element coverage.

Version zero requires a nonempty domain. This prevents an unchecked empty-domain assertion from becoming its own vacuity proof. An empty-domain universal may be added later only with an explicit trusted domain-construction boundary.

## Explicit finite domains

A finite domain is:

```text
SemanticFiniteDomain0(
  domainId,
  elementSort,
  cardinality,
  elements
)
```

The checker requires:

- a canonical domain identifier;
- a nonempty bounded element array;
- closed semantic terms only;
- one common declared element sort;
- canonical element order;
- no duplicate canonical term;
- `cardinality = elements.length` exactly;
- no undeclared `complete`, `exhaustive`, or similar assertion field.

The constructor sorts elements canonically for generator convenience, but the checker independently revalidates the order and uniqueness.

Domain elements may be semantic constants or closed semantic applications. Free variables are rejected inside the enumeration. Parameters may remain in the body judgment, but the bound variable is instantiated only by closed enumerated elements of its declared sort.

## Body templates and exact instances

The rule payload contains:

```text
variable : SemanticVar0
body     : SemanticEqJudgment0 | SemanticFormulaJudgment0
```

The variable sort must equal the domain element sort. For element `a`, the required case instance is computed by the existing capture-avoiding typed substitution operation:

```text
instance(a) = substituteSemanticJudgment0(body, variable, a)
```

The checker never accepts a caller-provided substitution result without recomputing it.

## Local exhaustion cases

For domain element at canonical index `i`, the local case record type is:

```text
FiniteExhaustCase0.<domainId>.<i>
```

It contains exactly:

```text
element
instance
```

`element` is the exact reflexive equality judgment for the enumerated term. `instance` is the exact body judgment after typed substitution at that term.

Every case must be an earlier accepted `Record.intro` node. Therefore the element binding and instantiated body are themselves backed by earlier accepted semantic proof nodes. The case cannot be supplied as a raw object or by a completion flag.

The checker rejects:

- a case with the wrong domain or index;
- a case for a different element;
- a body instance substituted at another element;
- a missing or extra field;
- a non-`Record.intro` premise;
- a duplicated, omitted, or reordered case.

## `FiniteExhaust.close`

A proof node has payload:

```text
op       = close
domain   = SemanticFiniteDomain0(...)
variable = SemanticVar0(...)
body     = semantic judgment template
```

It has exactly one case premise per domain element in canonical domain order.

The checker computes:

```text
SemanticFiniteExhaustJudgment0(
  domainId,
  elementSort,
  variable,
  body,
  elements,
  cardinality,
  universalJudgment = SemanticForallFiniteJudgment0(
    variable,
    elements,
    body
  ),
  caseProofIds,
  cases,
  canonicalEnumeration = true,
  allElementsCovered = true,
  noDuplicateElements = true,
  noOmittedElements = true,
  exactCardinality = true
)
```

Each case result records its exact index, element, and instantiated judgment. The supplied conclusion must be canonically identical to the computed object.

A caller cannot change the universal domain, mutate the body, falsify the cardinality, reorder cases, omit an element, duplicate an element, or replace an accepted case with a domain-completeness assertion.

## Rule-family composition

`CheckSemanticKernelProofFiniteExhaust0` validates a mixed proof DAG over:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
TraceInd
FiniteExhaust
```

in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofTraceInd0`;
2. every `FiniteExhaust` node is checked in original proof-DAG order against earlier accepted case records.

A predecessor rule that attempts to consume a `FiniteExhaust` conclusion is rejected because the filtered predecessor checker cannot resolve that dependency. Consumption remains unavailable until an explicit semantic rule defines it.

## Readiness result

The executable primitive rule families are now:

```text
Eq
Subst
Record
DAGInd
LedgerInd
OblTopoInd
TraceInd
FiniteExhaust
```

`CheckSemanticKernelReadinessFiniteExhaust0` removes `FiniteExhaust` from the computed missing-rule list but continues to reject final-theorem readiness. Eight primitive families remain:

```text
DPInd
Hall
RankInd
MinCounterexample
IntArith
Transport
TruthVec
FiniteRel
```

## Successor KImpl integration

`KImplSemanticFiniteExhaustSuccessor0` composes the merged TraceInd successor boundary:

1. it filters the full proof DAG to the seven predecessor rule families;
2. it requires `CheckKImplTraceIndSuccessor0` to accept that predecessor layer only as `development-only`;
3. it requires the exact predecessor supported-rule set;
4. it validates the full proof DAG with `CheckSemanticKernelProofFiniteExhaust0`;
5. it computes readiness with `CheckSemanticKernelReadinessFiniteExhaust0`;
6. it rejects final-theorem purpose while any primitive rule remains missing.

The input cannot supply semantic-ready booleans, missing-rule lists, final-emission flags, an external completeness assertion, or a weakened exhaustion policy.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-finiteexhaust-semantic0.test.mjs \
  test/pcc-kimpl-finiteexhaust-successor0.test.mjs
```

The tests cover:

- accepted canonical two-element exhaustion;
- exact computed universal-domain binding;
- duplicate-element rejection;
- noncanonical-order rejection;
- false-cardinality rejection;
- rejection of caller-supplied completeness flags;
- omitted-case rejection;
- swapped-case rejection;
- wrong-element substitution rejection;
- mutated universal-conclusion rejection;
- rejection of non-`Record.intro` case evidence;
- fail-closed rejection of predecessor rules consuming a `FiniteExhaust` conclusion;
- development-only successor acceptance;
- final-purpose rejection with eight primitive families still missing;
- caller readiness, stale predecessor, and policy-weakening rejection;
- preservation of the TraceInd-successor and legacy KImpl gates.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should be updated to consume `KImplSemanticFiniteExhaustSuccessor0`. Their fail-closed policies and final-node quarantine remain unchanged.

The next primitive rule after that integration is `DPInd`. It must bind an explicit finite state graph, canonical base states, predecessor-complete recurrence evidence, exact state values, a well-founded evaluation order, and a computed terminal dynamic-programming judgment without hiding an `argmin`, minimizer oracle, or unchecked optimum assertion.
