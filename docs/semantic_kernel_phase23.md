# Semantic kernel hardening — phase 23 (`IntArith`)

## Purpose

Phases 1–22 implemented semantic checking for `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, exact finite `LedgerInd`, obligation lifecycle induction, topological NAND `TraceInd`, explicit-domain `FiniteExhaust`, finite-state `DPInd`, exact finite-graph `Hall`, finite lexicographic `RankInd`, least-failure `MinCounterexample`, and successor KImpl/KBundle/global boundaries that keep every legacy final theorem node quarantined.

Phase 23 implements the next primitive PCC-K rule family, `IntArith`.

The report uses runtime integer fields for charge ledgers, budgets, cut-incidence masses, residual slack, ranks, table bounds, and arithmetic-cell certificates. These values must remain arithmetic data rather than finite profile-state symbols. The semantic rule therefore checks explicit bounded affine integer claims by exact replay. It does not trust caller truth flags, normalized values, comparison results, arithmetic certificates, optimization results, solver responses, searches, or oracle outputs.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`IntArith` proves ground, explicitly instantiated affine integer claims.

It is not a general-purpose theorem prover for quantified Presburger arithmetic. The checker evaluates one finite claim under one explicit environment. Symbolic universally quantified lemmas must be instantiated at the concrete certificate coordinates where they are used, or later represented by a separately checked theorem schema.

The rule supports exact affine combinations:

```text
constant + coefficient_1 * variable_1 + ... + coefficient_k * variable_k
```

where coefficients, constants, and environment values are canonical signed decimal strings. Variable-by-variable multiplication, division, nonlinear optimization, minimization, hidden search, and solver calls are not part of this rule.

## Canonical integer representation

Every integer is encoded as a canonical signed decimal string:

```text
0
7
-12
```

Rejected encodings include:

```text
+7
00
01
-0
-01
```

Input constants, coefficients, and bindings have an explicit decimal digit bound. Computed values are allowed a larger explicit result bound. JavaScript `Number` arithmetic is not used; the checker converts validated decimal strings to `BigInt`, evaluates exactly, then converts the result back to canonical decimal form.

## Affine terms and expressions

A term is:

```text
SemanticIntLinearTerm0(
  variable,
  coefficient
)
```

The coefficient must be nonzero.

An expression is:

```text
SemanticIntLinearExpr0(
  constant,
  terms
)
```

The checker requires:

- a bounded term array;
- unique variables;
- strict canonical variable-ID order;
- nonzero coefficients;
- no caller-supplied value, truth, normalization, certificate, solver, or result fields.

This representation is already a canonical affine normal form. Equivalent expressions with duplicate variables or unsorted terms are rejected rather than silently normalized from untrusted input.

## Environments

An environment is:

```text
SemanticIntEnvironment0(
  bindings
)
```

Each binding is:

```text
SemanticIntBinding0(
  variable,
  value
)
```

Bindings must be unique and in strict canonical variable-ID order.

The environment must bind exactly the union of variables appearing in the left and right expressions. Missing bindings and unused extra bindings reject. This prevents implicit defaults and untracked arithmetic inputs.

## Claims

A claim is:

```text
SemanticIntClaim0(
  claimId,
  relation,
  left,
  right
)
```

Supported relations are:

```text
eq
ne
lt
le
gt
ge
```

The claim record contains no expected truth value, evaluated values, comparison code, normalized difference, or external certificate.

## `IntArith.prove`

An `IntArith` proof node has payload:

```text
op          = prove
environment = SemanticIntEnvironment0(...)
claim       = SemanticIntClaim0(...)
```

The operation is closed: it accepts no proof premises. All arithmetic inputs are explicit in the canonical environment and claim. A node that supplies premises rejects rather than allowing an unrelated proof object to influence the arithmetic result.

The checker performs the following steps:

1. validate the canonical affine forms;
2. validate the canonical environment;
3. compute the exact required variable set;
4. require exact environment coverage;
5. evaluate both expressions with `BigInt`;
6. compute the signed difference and comparison code;
7. check the requested relation;
8. compute the canonical normalized affine difference `left - right`;
9. construct the complete terminal judgment.

A false ground claim rejects.

## Computed judgment

The accepted conclusion is exactly:

```text
SemanticIntArithJudgment0(
  claimId,
  relation,
  left,
  right,
  environment,
  variables,
  leftValue,
  rightValue,
  difference,
  comparison,
  normalizedDifference,
  relationVerified = true,
  canonicalAffineForms = true,
  exactEnvironmentCoverage = true,
  canonicalDecimalEncoding = true,
  exactBigIntEvaluation = true,
  boundedInputDigits = true,
  noSolverSearchOptimizationOrOracleUsed = true,
  terminalJudgmentComputed = true
)
```

The supplied conclusion must be canonically identical to the computed judgment. Mutating any value, relation, comparison code, environment, normalized coefficient, or audit flag rejects.

## Rule-family composition

`CheckSemanticKernelProofIntArith0` validates a mixed proof DAG over:

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
```

in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofMinCounterexample0`;
2. every `IntArith` node is checked in original proof-DAG order by exact closed evaluation.

A predecessor rule that attempts to consume an `IntArith` conclusion is rejected because the filtered predecessor checker cannot resolve that dependency. Consumption remains unavailable until an explicit semantic rule defines it.

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
```

`CheckSemanticKernelReadinessIntArith0` removes `IntArith` from the computed missing-rule list but continues to reject final-theorem readiness. Three primitive families remain:

```text
Transport
TruthVec
FiniteRel
```

## Successor KImpl integration

`KImplSemanticIntArithSuccessor0` composes the merged MinCounterexample successor boundary:

1. it filters the full proof DAG to the twelve predecessor rule families;
2. it requires `CheckKImplMinCounterexampleSuccessor0` to accept that predecessor layer only as `development-only`;
3. it requires the exact MinCounterexample-era supported-rule set;
4. it validates the full proof DAG with `CheckSemanticKernelProofIntArith0`;
5. it computes readiness with `CheckSemanticKernelReadinessIntArith0`;
6. it rejects final-theorem purpose while any primitive family remains missing.

Caller readiness fields, stale MinCounterexample-only records, weakened arithmetic policies, and legacy structural failures reject.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-intarith-semantic0.test.mjs \
  test/pcc-kimpl-intarith-successor0.test.mjs
```

The tests cover:

- exact affine evaluation beyond the `Number` safe-integer range;
- all-empty-variable constant comparison;
- canonical decimal encoding;
- nonzero coefficients and canonical variable order;
- exact environment coverage;
- false-claim rejection;
- unsupported relation rejection;
- caller truth and solver assertion rejection;
- premise rejection for closed arithmetic evaluation;
- mutated conclusion rejection;
- explicit digit bounds;
- fail-closed rejection of predecessor rules consuming an IntArith conclusion;
- development-only successor acceptance;
- final-purpose rejection with three primitive families still missing;
- caller readiness, stale predecessor, policy weakening, and legacy KImpl rejection.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should consume `KImplSemanticIntArithSuccessor0`. Their fail-closed policies and final-node quarantine remain unchanged.

The next primitive rule after that integration is `Transport`. It must bind explicit source and target carriers or modes, an accepted source judgment, a declared transport map, every preservation obligation required by the judgment kind, and an exact computed target judgment. Quotient equality must remain nonconstructive unless a checked full lift and all lost-bit or finite-kernel obligations are discharged.
