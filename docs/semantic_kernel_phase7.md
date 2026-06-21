# Semantic kernel hardening — phase 7 (`LedgerInd`)

## Purpose

Phases 1–6 implemented semantic `Eq`, typed capture-avoiding `Subst`, canonical `Record`, predecessor-complete `DAGInd`, successor KImpl boundaries, and successor KBundle/global gates that quarantine legacy final theorem nodes.

Phase 7 implements the next primitive PCC-K rule family, `LedgerInd`.

The proof report names ledger induction as a primitive rule and relies on charge, obligation, route, mass, selector-silence, no-lower, and replay ledgers. A semantic ledger rule must therefore check every finite ledger position, bind every local transition proof, preserve exact immediate-predecessor state, and compute one exact terminal closure. It must not accept a list merely because the list is finite or because a caller sets a `complete` flag.

This phase does not modify the sealed `7072f8d` source/checker or artefact release.

## Interpretation boundary

`LedgerInd` is a structural induction rule over an already proved finite ledger. It does not invent or validate the domain-specific meaning of a local transition.

For every ledger position, the following must already be accepted semantic judgments:

- the declared ledger entry;
- the declared local transition theorem;
- the current invariant;
- for non-base positions, the exact invariant closed at the immediately preceding position.

The local case must itself be accepted `Record.intro` evidence containing those judgments. Future semantic rules such as `IntArith`, `Transport`, `TruthVec`, and `FiniteRel` are responsible for proving domain-specific transition judgments. `LedgerInd` only chains accepted local theorems without omission, substitution, or reordering.

## Finite ledger syntax

A ledger is:

```text
SemanticLedger0(
  ledgerId,
  [SemanticLedgerEntry0(...), ...]
)
```

Each entry contains:

```text
index
id
previousId
entry
transition
```

The checker requires:

- a nonempty bounded entry list;
- consecutive indices beginning at zero;
- canonical unique entry identifiers;
- `previousId = null` at index zero;
- every later `previousId` to name the immediately preceding entry;
- the entry and transition fields to be semantic judgment objects;
- no undeclared ledger or entry properties.

This is a linear ledger. Branching finite dependencies remain the responsibility of `DAGInd` or later specialized induction rules.

## Local case evidence

For ledger entry `e`, the local case record type is:

```text
LedgerIndCase0.<ledgerId>.<entryId>
```

The base case contains exactly these canonical fields:

```text
current
entry
transition
```

Every non-base case contains exactly:

```text
current
entry
previous
transition
```

The checker requires:

- the case premise to be an earlier accepted `Record.intro` node;
- `entry` to be canonically identical to the entry judgment declared in the ledger;
- `transition` to be canonically identical to the declared local transition judgment;
- `previous` to be canonically identical to the invariant closed at the immediately preceding ledger entry;
- `current` to be an accepted semantic judgment object.

A bare record-shaped object, a projection, a different rule family, or a caller-supplied transition-complete flag is rejected.

## `LedgerInd.close`

A `LedgerInd` proof node has payload:

```text
op = close
ledger = SemanticLedger0(...)
```

and exactly one local case premise per ledger entry, in ledger order.

The checker derives:

```text
SemanticLedgerIndJudgment0(
  ledgerId,
  entryOrder,
  baseEntryId,
  finalEntryId,
  caseProofIds,
  cases,
  baseInvariant,
  finalInvariant,
  allEntriesClosed = true
)
```

Each derived case records the exact entry, local transition theorem, immediate predecessor coordinate, and closed invariant. The supplied conclusion must be canonically identical to the computed object.

The conclusion cannot skip an entry, reorder case proofs, change the terminal entry, substitute a transition theorem, alter a previous state, or claim a different final invariant.

## Rule-family composition

`CheckSemanticKernelProofLedgerInd0` validates a mixed

```text
Eq / Subst / Record / DAGInd / LedgerInd
```

proof DAG in two layers:

1. the filtered predecessor sub-DAG must pass `CheckSemanticKernelProofDAGInd0`;
2. every `LedgerInd` node is checked in original proof-DAG order against earlier accepted case records.

An earlier rule family that attempts to consume a `LedgerInd` conclusion is rejected by the filtered predecessor checker. Such use remains unavailable until an explicit semantic rule defines it.

## Readiness result

The executable semantic rule families are now:

```text
Eq
Subst
Record
DAGInd
LedgerInd
```

`CheckSemanticKernelReadinessLedgerInd0` removes `LedgerInd` from the missing-rule list but continues to reject final-theorem readiness. Eleven primitive families remain:

```text
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

`KImplSemanticLedgerIndSuccessor0` composes the merged DAGInd successor boundary:

1. it filters the full proof DAG to `Eq`, `Subst`, `Record`, and `DAGInd` nodes;
2. it requires `CheckKImplDAGIndSuccessor0` to accept that predecessor layer only as `development-only`;
3. it validates the full proof DAG with `CheckSemanticKernelProofLedgerInd0`;
4. it computes readiness with `CheckSemanticKernelReadinessLedgerInd0`;
5. it rejects final-theorem purpose while any primitive rule remains missing.

The input cannot provide semantic-ready booleans, missing-rule lists, public-emission flags, or a weakened policy.

## Verification targets

Durable CI runs:

```bash
node --test \
  test/pcc-kernel-ledgerind-semantic0.test.mjs \
  test/pcc-kimpl-ledgerind-successor0.test.mjs
```

The tests cover:

- accepted three-position ledger closure;
- exact base and final invariant extraction;
- rejection of a substituted previous invariant;
- rejection of a missing previous field;
- rejection of wrong entry and transition judgments;
- rejection of skipped `previousId` coordinates;
- rejection of swapped case-proof order;
- rejection of a mutated terminal conclusion;
- rejection of non-`Record.intro` local evidence;
- fail-closed rejection of predecessor rules consuming `LedgerInd` conclusions;
- development-only successor acceptance;
- final-purpose rejection with eleven rule families still missing;
- caller readiness and policy-weakening rejection;
- preservation of DAGInd-successor and legacy KImpl gates.

## Next step

After this phase is accepted, the successor KBundle and successor global proof-DAG gate should be updated to consume `KImplSemanticLedgerIndSuccessor0`. Their fail-closed policies do not change: legacy conformance, Sigma, reflection, package, and final nodes remain structural-only and quarantined.

The next primitive rule after that integration is `OblTopoInd`, which must check exact obligation creation, dependency order, permitted discharge evidence, full-mode discharge requirements, and terminal absence of open obligations.
