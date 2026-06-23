# Semantic kernel hardening — phase 29 (`FiniteRel`)

## Purpose

Phases 1–28 implemented semantic checking for every PCC-K primitive except `FiniteRel`, including exact bounded `TruthVec.evaluate` over canonical NAND truth vectors and the TruthVec-expanded successor KBundle/global gates.

Phase 29 implements the final primitive PCC-K rule family, `FiniteRel`, and carries it through the successor KImpl boundary.

The rule evaluates explicit finite relations over canonical finite domains. It computes relation literals, identity, converse, composition, coordinate restriction, union, intersection, difference, transitive closure, reflexive-transitive closure, equality claims, inclusion claims, reflexivity claims, transitivity claims, and closure claims. It does not trust caller-supplied relation results, equality flags, inclusion flags, closure flags, completeness flags, normalization claims, solver responses, searches, optimizations, or oracle outputs.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`FiniteRel` is a bounded finite evaluator over declared finite domains. It is not an external relational-algebra oracle.

A certificate supplies:

- explicit finite domains;
- explicit relation nodes in evaluation order;
- literal tuple sets in canonical tuple order;
- computed relation nodes whose results must be recomputed by the checker;
- explicit claims that are accepted only if the checker computes them as true.

The checker independently evaluates every relation node and every claim. The supplied conclusion must exactly equal the computed relation and claim ledger.

## Domains

A domain is:

```text
SemanticFiniteRelDomain0(index, id, elements)
```

The checker requires:

- exact consecutive domain indices;
- canonical unique domain IDs;
- bounded element arrays;
- unique canonical element IDs;
- canonical element order.

The domain order determines tuple order, restriction order, identity order, composition output order, and closure output order.

## Tuples and relation nodes

A tuple is:

```text
SemanticFiniteRelTuple0(index, values)
```

A relation node is:

```text
SemanticFiniteRelNode0(
  index,
  id,
  op,
  domainIds,
  inputIds,
  tuples,
  restrictions
)
```

Supported node operations are:

```text
literal
identity
converse
compose
restrict
union
intersection
difference
transitive-closure
reflexive-transitive-closure
```

The checker requires:

- exact consecutive relation-node indices;
- unique canonical node IDs;
- declared coordinate domains;
- nonempty bounded arity;
- earlier-only relation dependencies;
- exact tuple arity;
- tuple values inside the declared coordinate domains;
- literal tuples unique and in canonical domain order;
- computed nodes with no caller-supplied result tuples;
- coordinate restrictions only for the restriction operation;
- exact signatures for identity, converse, composition, set operations, and closure operations;
- bounded relation universe and bounded total relation-cell budget.

## Computed operations

`identity` computes the binary endorelation `{(x,x)}` in domain order.

`converse` reverses every binary tuple.

`compose` computes `{(a,c) : exists b, (a,b) in R and (b,c) in S}` and enforces exact middle-domain matching.

`restrict` filters tuples by one allowed-element set per coordinate. The allowed sets must be unique and in canonical domain order.

`union`, `intersection`, and `difference` are computed as exact finite set operations on tuple keys.

`transitive-closure` computes the least transitive superset of a binary endorelation by bounded finite closure.

`reflexive-transitive-closure` first adds identity and then computes transitive closure.

All computed relation tuples are canonicalized into the declared output signature order.

## Claims

A claim is:

```text
SemanticFiniteRelClaim0(index, id, claimKind, leftId, rightId)
```

Supported claim kinds are:

```text
equal
included
reflexive
transitive
reflexive-transitive-closed
```

Equality and inclusion claims require identical relation signatures. Reflexivity and transitivity claims require binary endorelations. A claim result is accepted only when the checker computes `holds = true`. A false claim rejects rather than appearing as a negative result in an accepted proof node.

## `FiniteRel.verify`

A `FiniteRel` proof node has payload:

```text
op   = verify
spec = SemanticFiniteRelSpec0(...)
```

The operation is closed and accepts no proof premises. Every finite input is contained in the checked program. This prevents earlier proof nodes from smuggling relation equality, closure, or completeness results into the primitive checker.

## Computed judgment

The accepted conclusion is exactly:

```text
SemanticFiniteRelJudgment0(
  evaluationId,
  program,
  relations,
  claims,
  domainCount,
  relationNodeCount,
  claimCount,
  programDigest,
  relationDigest,
  claimDigest,
  canonicalFiniteDomains = true,
  exactTupleArity = true,
  exactTupleOrder = true,
  everyRelationComputed = true,
  identityConverseCompositionRestrictionComputed = true,
  equalityInclusionAndClosureComputed = true,
  allClaimsHold = true,
  boundedEvaluation = true,
  noSolverSearchOptimizationOrOracleUsed = true,
  terminalJudgmentComputed = true
)
```

Mutating any relation tuple, tuple order, relation signature, claim result, digest, count, or audit flag rejects.

## Rule-family composition

`CheckSemanticKernelProofFiniteRel0` validates a mixed proof DAG over:

```text
Eq
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

in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofTruthVec0`;
2. every `FiniteRel` node is checked in original proof-DAG order by exact bounded finite relation evaluation.

A predecessor rule that attempts to consume a `FiniteRel` conclusion is rejected because the filtered predecessor checker cannot resolve that dependency. Consumption remains unavailable until an explicit semantic rule defines it.

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
DPInd
Hall
RankInd
MinCounterexample
IntArith
Transport
TruthVec
FiniteRel
```

`CheckSemanticKernelReadinessFiniteRel0` computes an empty missing-rule list and accepts primitive semantic coverage.

## Successor KImpl integration

`KImplSemanticFiniteRelSuccessor0` composes the merged TruthVec successor boundary:

1. it filters the full proof DAG to the fifteen predecessor rule families;
2. it requires `CheckKImplTruthVecSuccessor0` to accept that predecessor layer only as `development-only`;
3. it requires the exact TruthVec-era supported-rule set;
4. it validates the full proof DAG with `CheckSemanticKernelProofFiniteRel0`;
5. it computes readiness with `CheckSemanticKernelReadinessFiniteRel0`;
6. it accepts explicit KImpl final-theorem purpose because primitive-rule coverage is now complete.

Development-purpose records remain development-only even though the primitive semantic kernel is ready. Final-purpose records are KImpl-final-ready only at the KImpl boundary. KBundle, global proof-DAG, Sigma, reflection, package, and legacy final theorem nodes remain separately gated.

Caller readiness fields, stale TruthVec-only records, weakened FiniteRel policies, false relation claims, and legacy structural failures reject.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-finiterel-semantic0.test.mjs \
  test/pcc-kimpl-finiterel-successor0.test.mjs
```

The tests cover:

- relation literal validation;
- identity, converse, composition, restriction, union, intersection, difference, transitive closure, and reflexive-transitive closure;
- equality, inclusion, transitivity, and closure claims;
- noncanonical tuple order;
- composition signature mismatch;
- caller-supplied result tuples;
- false claims;
- caller equality and completion assertions;
- mutated conclusion rejection;
- premise rejection for closed finite computation;
- fail-closed rejection of predecessor rules consuming a FiniteRel conclusion;
- readiness acceptance with no missing primitive rules;
- development-only successor acceptance;
- explicit KImpl final-readiness acceptance;
- caller readiness, stale predecessor, policy weakening, and legacy KImpl rejection.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should consume `KImplSemanticFiniteRelSuccessor0`.

That integration must preserve the final-node quarantine until the remaining semantic surfaces are active: K0 semantic conformance, Sigma derivations, reflection soundness, and semantic global-node derivations.
