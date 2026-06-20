# Semantic kernel hardening — phase 3 (successor KImpl readiness)

## Purpose

Phases 1 and 2 implemented semantic checking for `Eq` and typed capture-avoiding `Subst`. The next requirement is architectural: partial semantic work must remain usable for development, but it must be impossible to treat a structurally accepted legacy `KImpl0` as ready for a successor final theorem.

This phase adds a separate successor envelope and two fail-closed checkers. It does not modify the sealed `7072f8d` checker or artefact release.

## Successor record

`KImplSemanticSuccessor0` contains:

```text
Purpose              development | final-theorem
KImpl                legacy KImpl0 record
SemanticKernel       fixed checker binding plus semantic ProofDAG
Policy               fixed fail-closed release policy
```

The checker computes all readiness fields. The input is not allowed to contain caller-supplied fields such as `semanticKernelReady`, `missingRules`, `finalTheoremReady`, or `publicTheoremEmissionAllowed`.

The fixed release policy states:

```text
development may use a partial semantic kernel
final-theorem use requires complete semantic rule coverage
public theorem emission requires final-theorem readiness
legacy structural acceptance is not semantic readiness
```

Attempts to weaken or replace that policy reject at the input boundary.

## Checker split

### `CheckKImplSuccessor0`

This is the development-facing checker. It performs, in order:

1. exact successor-envelope and policy validation;
2. equality of the legacy and semantic primitive-rule universes;
3. legacy `CheckKImpl0` structural validation;
4. semantic proof-DAG validation through `CheckSemanticKernelProof0`;
5. semantic readiness computation through `CheckSemanticKernelReadiness0`.

A development-purpose record may accept while readiness is incomplete, but its normal form is forced to record:

```text
status = development-only
semanticKernelReady = false
finalTheoremReady = false
publicTheoremEmissionAllowed = false
```

A final-theorem-purpose record rejects unless semantic readiness accepts.

### `CheckKImplFinalTheoremReadiness0`

This is the explicit successor final-theorem gate. It first requires `Purpose = final-theorem`; a development record cannot be reused at this boundary. It then performs the same checks and rejects if any primitive semantic rule remains unimplemented.

No configuration or input field can disable this requirement.

## Current machine result

The semantic handler universe is currently:

```text
Eq
Subst
```

The legacy and semantic required-rule universes both contain the same sixteen primitive rule names. The readiness checker therefore continues to reject because fourteen handlers remain absent:

```text
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

This is an intended release block, not a test failure.

## Security and soundness properties

The successor boundary is designed to prevent several specific fail-open paths:

- a legacy `CheckKImpl0` acceptance cannot be re-labelled as semantic readiness;
- a valid partial semantic proof cannot imply complete primitive-rule coverage;
- a development-purpose record cannot satisfy the final-theorem checker;
- fake readiness booleans and fake missing-rule lists are rejected;
- a weakened release policy is rejected;
- an invalid semantic proof rejects even in development mode;
- a malformed legacy KImpl still rejects before semantic readiness is considered;
- divergence between the legacy primitive-rule list and the semantic required-rule list rejects.

## Verification

The targeted CI suite includes:

```bash
node --test test/pcc-kimpl-successor0.test.mjs
```

The tests cover development-only acceptance, final-purpose rejection, explicit final-gate rejection, caller-supplied readiness rejection, policy weakening rejection, invalid semantic proof rejection, and preservation of legacy KImpl structural checks.

## Remaining integration work

This phase creates the enforceable KImpl readiness boundary but does not yet replace the legacy KImpl call sites in the final package chain. The next steps are:

1. add a successor KBundle that contains `KImplSemanticSuccessor0` and its accepted development or final record;
2. migrate primitive conformance nodes to the semantic proof syntax, beginning with `Record`;
3. require `CheckKImplFinalTheoremReadiness0 = accept` in a successor global proof DAG and release gate;
4. replace assertion-shaped Sigma and reflection records with semantic derivations;
5. publish the completed chain under new immutable source/checker and artefact coordinates.

Until those steps and all remaining rule handlers are complete, no successor final theorem may be emitted.
