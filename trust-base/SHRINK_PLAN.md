# Trust-base shrink plan

> **Superseded trust-base plan:** This June 2026 roadmap belongs to the historical JavaScript
> assertion-checker stack. It is not the current formal reconstruction plan or blocker inventory.
> See [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json)
> and [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

The historical plan proposed shrinking its trust base by replacing broad assumptions with smaller
executable ledgers, independent replays, and formal statement skeletons.

Historical machine-readable coordinate:

```text
PNP-TRUST-BASE-SHRINK-PLAN-2026-06-27-01
```

Machine-readable file:

```text
trust-base/SHRINK_PLAN.json
```

Audit command:

```bash
node pcc-trust-base-shrink-plan0.mjs --json
```

## Historical boundary

The recorded shrink plan was non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

`shrinksTrustBaseNow = false` means this file is a roadmap and audit object. A later PR must mark a task complete only when its deliverables, acceptance criteria, and checker integration are present.

## Planned tasks

### TB-001: bounded integer validation

Replace implicit JavaScript integer assumptions with explicit safe-integer and finite-bound validation at checker boundaries.

### TB-002: canonicalization cross-check

Cross-check `stableStringify0` with an independent Python canonicalization implementation over a fixture corpus.

### TB-003: independent SHA256 comparison

Compare JS and Python SHA256 digests over the same canonical byte payloads.

### TB-004: second-runtime proof replay

Expand the Python verifier to replay more checker families and boundary-negative fixtures.

### TB-005: Lean or Coq statement skeletons

Generate formal statement skeletons for NAND direct-wire semantics, compatible replacement, locked NAND thresholding, and the complexity implication.

### TB-006: executable NAND direct-wire semantics

Materialize `semantics/nand-direct-wire-spec.json`, `semantics/nand-direct-wire-reference.mjs`, and exhaustive small-model tests.

### TB-007: small locked-NAND SAT truth-table verification

For bounded CNF instances, brute-force SAT and compare against the locked-NAND threshold predicate.

## What counts as progress

A trust-base task moves from `planned` to `represented` when it has source files, tests, and a checker verdict. It moves to `complete` only when the corresponding assumption is narrowed in `trust-base/TRUST_BASE.json` and accepted by `pcc-trust-base0.mjs`.

This plan did not say the trust base was empty. Its recorded reduction queue is historical. Current
work is governed by the concrete obligations in the formal-reconstruction status.
