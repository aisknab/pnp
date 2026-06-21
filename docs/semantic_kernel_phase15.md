# Semantic kernel hardening — phase 15 (`DPInd`)

## Purpose

Phases 1–14 implemented semantic checking for `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, exact finite `LedgerInd`, obligation lifecycle induction, topological NAND `TraceInd`, explicit-domain `FiniteExhaust`, successor KImpl boundaries, and KBundle/global gates that quarantine every legacy final theorem node.

Phase 15 implements the next primitive PCC-K rule family, `DPInd`.

The report uses dynamic programs in the unary full/projected lift analysis, exact budget-envelope computation, finite transition systems, and other schedule-bounded constructions. A semantic dynamic-programming rule must bind a displayed finite state graph, check a well-founded evaluation order, bind every recurrence to all of its declared predecessors, require accepted local equation evidence, and compute the terminal result. It must not accept an `argmin`, minimizer oracle, hidden optimum flag, or a claimed `complete = true` field as a replacement for recurrence evidence.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`DPInd` is structural induction over an explicit finite recurrence graph.

It does not prove the domain-specific semantics of a recurrence operator. Each base equation and recurrence equation must already be an accepted semantic judgment. The rule checks that those judgments are assembled in the exact state order with exact predecessor values.

Arithmetic evaluation, comparison, finite minimizer selection, relation semantics, and mode transport remain the responsibility of the semantic rules that prove the local equations. In particular:

- `FiniteExhaust` may establish explicit finite candidate coverage;
- future `IntArith` may establish integer comparisons and arithmetic identities;
- future `FiniteRel` may establish finite transition relations;
- future `Transport` may establish cross-carrier or cross-mode transfer.

`DPInd` cannot turn an unchecked optimization assertion into an accepted terminal value.

## Explicit finite DP programs

A DP program is:

```text
SemanticDPProgram0(
  programId,
  valueSort,
  states,
  terminalStateId,
  terminalCoordinate
)
```

The checker requires:

- a nonempty bounded state array;
- canonical unique state IDs;
- exact consecutive state indices `0, ..., n-1`;
- one common closed value sort;
- a nonempty canonical prefix of base states;
- recurrence states only after the base prefix;
- every recurrence predecessor to be an earlier state;
- unique predecessor IDs in earlier-state evaluation order;
- the terminal state to be the final evaluation coordinate;
- every declared state to lie in the reverse dependency closure of the terminal state;
- no undeclared completeness, optimum, minimizer, search, or oracle field.

The reverse-closure requirement prevents dead states from being counted as evidence for a terminal computation they do not influence.

## Base states

A base state is:

```text
SemanticDPState0(
  stateKind = base,
  index,
  id,
  predecessorIds = [],
  operator = null,
  baseTerm,
  recurrenceTerm = null,
  value,
  equation = value = baseTerm
)
```

Both `value` and `baseTerm` must be closed semantic terms of the program value sort. The equation must bind them in the exact declared orientation.

Base states form a single prefix. Their IDs are in canonical identifier order. A late base state cannot be inserted after recurrence evaluation begins.

## Recurrence states

A recurrence state is:

```text
SemanticDPState0(
  stateKind = step,
  index,
  id,
  predecessorIds = [p0, ..., pk],
  operator,
  baseTerm = null,
  recurrenceTerm = operator(value(p0), ..., value(pk)),
  value,
  equation = value = recurrenceTerm
)
```

The checker independently reconstructs `recurrenceTerm` from the already declared predecessor values. A caller cannot omit a predecessor from the term, substitute another state value, reorder predecessor arguments, or reference a forward state.

Version zero rejects operator identifiers that encode hidden optimization or search, including minimization, maximization, optimum, oracle, solver, and search aliases. A genuine finite optimum recurrence must be decomposed into explicit candidate coverage and accepted comparison/selection evidence rather than hidden behind an operator name.

## Local state cases

For state `s` in program `P`, the local case record type is:

```text
DPIndCase0.<P>.<s>
```

It contains exactly:

```text
equation
value
dep.<predecessor-id> ...
```

The `equation` field is the exact declared base or recurrence equation. The `value` field is the exact reflexive binding of the state value. Every dependency field is the exact value binding previously evaluated for that predecessor.

Every case must be an earlier accepted `Record.intro` node. Therefore all state equations, state values, and predecessor values are backed by accepted semantic proof nodes. A raw case object, a completion flag, or an optimum assertion is not evidence.

The checker rejects:

- a case for the wrong program or state;
- a missing or extra predecessor field;
- a substituted predecessor value;
- a wrong base or recurrence equation;
- a case supplied out of state order;
- a non-`Record.intro` premise.

## `DPInd.close`

A `DPInd` proof node has payload:

```text
op      = close
program = SemanticDPProgram0(...)
```

and exactly one case premise per state in evaluation order.

The checker computes:

```text
SemanticDPIndJudgment0(
  programId,
  valueSort,
  stateOrder,
  baseStateIds,
  stepStateIds,
  stateCount,
  baseStateCount,
  stepStateCount,
  terminalStateId,
  terminalCoordinate,
  terminalValue,
  terminalJudgment = SemanticDPResultJudgment0(...),
  caseProofIds,
  cases,
  canonicalBasePrefix = true,
  evaluationOrderWellFounded = true,
  predecessorCoverageComplete = true,
  recurrenceEvidenceExact = true,
  allStatesEvaluated = true,
  allStatesContributeToTerminal = true,
  hiddenOptimizationAbsent = true,
  terminalStateComputed = true
)
```

The supplied conclusion must be canonically identical to this computed object. A caller cannot mutate the terminal coordinate, replace the terminal value, reorder cases, omit a state, add a dead state, or assert an optimum outside the checked recurrence graph.

## Rule-family composition

`CheckSemanticKernelProofDPInd0` validates a mixed proof DAG over:

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
```

in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofFiniteExhaust0`;
2. every `DPInd` node is checked in original proof-DAG order against earlier accepted case records.

A predecessor rule that attempts to consume a `DPInd` conclusion is rejected because the filtered predecessor checker cannot resolve that dependency. Consumption remains unavailable until an explicit semantic rule defines it.

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
```

`CheckSemanticKernelReadinessDPInd0` removes `DPInd` from the computed missing-rule list but continues to reject final-theorem readiness. Seven primitive families remain:

```text
Hall
RankInd
MinCounterexample
IntArith
Transport
TruthVec
FiniteRel
```

## Successor KImpl integration

`KImplSemanticDPIndSuccessor0` composes the merged FiniteExhaust successor boundary:

1. it filters the full proof DAG to the eight predecessor rule families;
2. it requires `CheckKImplFiniteExhaustSuccessor0` to accept that predecessor layer only as `development-only`;
3. it requires the exact predecessor supported-rule set;
4. it validates the full proof DAG with `CheckSemanticKernelProofDPInd0`;
5. it computes readiness with `CheckSemanticKernelReadinessDPInd0`;
6. it rejects final-theorem purpose while any primitive rule remains missing.

The input cannot supply semantic-ready booleans, missing-rule lists, final-emission flags, optimum assertions, minimizer or oracle fields, or a weakened DP policy.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-dpind-semantic0.test.mjs \
  test/pcc-kimpl-dpind-successor0.test.mjs
```

The tests cover:

- accepted base and recurrence closure over an explicit terminal-connected state DAG;
- exact computed state order, base prefix, recurrence values, and terminal result;
- forward-predecessor rejection;
- late-base rejection;
- nonconsecutive-index rejection;
- omitted recurrence argument rejection;
- hidden `argmin`/oracle operator rejection;
- dead-state rejection;
- caller optimum/completion assertion rejection;
- missing or substituted predecessor case evidence;
- swapped case rejection;
- mutated terminal-conclusion rejection;
- rejection of non-`Record.intro` local evidence;
- fail-closed rejection of predecessor rules consuming a `DPInd` conclusion;
- development-only successor acceptance;
- final-purpose rejection with seven primitive families still missing;
- caller readiness, stale predecessor, policy weakening, and legacy KImpl rejection.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should be updated to consume `KImplSemanticDPIndSuccessor0`. Their fail-closed policies and final-node quarantine remain unchanged.

The next primitive rule after that integration is `Hall`. It must bind an explicit finite bipartite graph, canonical neighbourhood computation, either a complete matching or an exact Hall-deficient witness, and a computed terminal matching judgment without trusting a caller-supplied matching-complete flag.
