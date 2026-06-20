# Semantic kernel hardening — phase 5 (`DAGInd`)

## Purpose

Phases 1–4 implemented semantic `Eq`, typed capture-avoiding `Subst`, canonical `Record`, and fail-closed successor KImpl boundaries. Phase 5 implements the structural content of the primitive `DAGInd` rule.

The report uses DAG induction for finite proof DAGs and displayed evaluator DAGs. A sound DAG-induction rule must not merely accept an acyclic list. It must bind a finite graph, require every local case, require every predecessor invariant at every step, and compute one exact all-node conclusion.

This phase does not modify the sealed `7072f8d` release.

## Scope of the primitive

`DAGInd` is a structural closure rule. It does **not** prove a local node invariant from arbitrary payload data. Each local invariant must already be an accepted semantic judgment, and each local case must already be accepted `Record.intro` evidence.

This separation is intentional:

- existing and future semantic rules establish the local invariant;
- `Record.intro` binds that invariant to all predecessor invariants;
- `DAGInd.close` verifies finite predecessor-complete closure over the whole DAG.

The rule therefore cannot turn an assertion-shaped node payload into a theorem.

## Finite induction graph

A graph is:

```text
SemanticInductionDAG0(
  graphId,
  [SemanticInductionDAGNode0(id, predecessors), ...]
)
```

The checker requires:

- a nonempty, bounded node set;
- canonical identifiers;
- unique node identifiers;
- canonical increasing topological order;
- unique, canonically ordered predecessor lists;
- every predecessor to be an earlier graph node;
- bounded predecessor count and total edge count;
- no undeclared graph or graph-node fields.

The increasing identifier order is part of the canonical representation. A graph generator must assign identifiers compatible with its topological order.

## Local case evidence

For graph node `v` with predecessors `u1, ..., uk`, the corresponding local case is a `SemanticRecordJudgment0` of type:

```text
DAGIndCase0.<graphId>.<v>
```

with exactly these canonical fields:

```text
current
pred.<u1>
...
pred.<uk>
```

The `current` field contains the already accepted invariant for `v`. Every `pred.<u>` field must be canonically identical to the invariant closed for predecessor `u`.

The case must itself be an earlier accepted `Record.intro` proof node. A bare record-shaped object, an Eq node, a projection, or a caller-supplied case flag is rejected.

Source nodes have no predecessor fields. Non-source nodes must name every graph predecessor exactly once; missing, duplicated, substituted, or stale predecessor invariants reject.

## `DAGInd.close`

A `DAGInd` proof node has payload:

```text
op = close
graph = SemanticInductionDAG0(...)
```

and exactly one premise per graph node, in graph-node order. The checker derives the conclusion:

```text
SemanticDAGIndJudgment0(
  graphId,
  nodeOrder,
  sourceNodeIds,
  sinkNodeIds,
  caseProofIds,
  cases,
  allNodesClosed = true
)
```

Each case result records the node id, exact predecessor list, and accepted current invariant. The supplied conclusion must be canonically identical to this computed object.

The conclusion cannot omit a node, reorder cases, alter a source or sink set, replace an invariant, or claim closure over a different graph.

## Rule-family composition

`CheckSemanticKernelProofDAGInd0` validates a mixed `Eq`/`Subst`/`Record`/`DAGInd` proof DAG in two layers:

1. the filtered `Eq`/`Subst`/`Record` sub-DAG must pass `CheckSemanticKernelProofRecord0`;
2. every `DAGInd` node is checked in original proof-DAG order against earlier accepted case records.

An `Eq`, `Subst`, or `Record` node that attempts to consume a `DAGInd` conclusion is rejected by the filtered predecessor checker. Such use remains unavailable until an explicit semantic rule defines it.

## Readiness result

The executable semantic rule families are now:

```text
Eq
Subst
Record
DAGInd
```

`CheckSemanticKernelReadinessDAGInd0` removes `DAGInd` from the missing-rule list but continues to reject final-theorem readiness. Twelve primitive families remain:

```text
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

## Successor KImpl integration

`KImplSemanticDAGIndSuccessor0` composes the merged Record successor boundary:

1. it filters the full proof DAG to `Eq`/`Subst`/`Record` nodes;
2. it requires `CheckKImplRecordSuccessor0` to accept that predecessor layer only as `development-only`;
3. it validates the full proof DAG with `CheckSemanticKernelProofDAGInd0`;
4. it computes readiness with `CheckSemanticKernelReadinessDAGInd0`;
5. it rejects final-theorem purpose while any primitive rule remains missing.

The input cannot provide readiness booleans, missing-rule lists, public-emission flags, or a weakened release policy.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-dagind-semantic0.test.mjs \
  test/pcc-kimpl-dagind-successor0.test.mjs
```

The tests cover:

- accepted source and multi-predecessor closure;
- exact source and sink computation;
- rejection of a substituted predecessor invariant;
- rejection of a missing predecessor case field;
- rejection of swapped case proofs;
- rejection of forward edges and noncanonical topological order;
- rejection of a mutated all-node conclusion;
- rejection of non-Record local case evidence;
- fail-closed rejection of predecessor rules consuming DAGInd conclusions;
- development-only successor acceptance;
- final-purpose rejection with twelve rules still missing;
- caller readiness and policy-weakening rejection;
- preservation of Record-successor and legacy KImpl gates.

## Next step

After this phase is accepted, the next architectural step is a successor KBundle and successor global proof-DAG gate that carry the computed KImpl semantic-readiness record instead of the legacy assertion-shaped kernel status. That integration must remain development-only until all twelve remaining rule families, Sigma derivations, and reflection soundness are complete.
