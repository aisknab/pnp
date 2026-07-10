# Gap ledger

> **Superseded ledger:** This June 2026 gap ledger is preserved as historical assertion-checker
> evidence. Its release-policy blockers are not the current formal blocker inventory. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-GAP-LEDGER-2026-06-27-01
```

Machine-readable ledger:

```text
proof-obligations/GAP_LEDGER.json
```

Checker:

```bash
node pcc-gap-ledger0.mjs --json
```

The gap ledger recorded unresolved, externally trusted, bounded-seed-only, and release-policy items
for the historical checker stack. Later checker transitions did not formally prove their mathematics.

## Status classes

```text
blocked-release-gap
known-unresolved
represented-not-discharged
explicit-external-trust
bounded-seed-only
reproducibility-hardening-gap
```

## Historical activation blockers

The historical ledger recorded these release blockers:

```text
Release.UnrestrictedFinalSoundness
ExternalReview.Acceptance
```

They are not cleared by bounded small-model evidence, source-surface seed audits, proof-obligation mapping, or reproducibility infrastructure.

## Non-activation boundary

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

The gap ledger is not a theorem activation event. It is a map of what remains explicit, what is externally trusted, what is represented but not discharged, and what must be eliminated or downgraded before public theorem emission can be enabled.

The current reconstruction replaces this checker-release plan with concrete formal definitions,
theorems, runtime bounds, and an assumption-audited Lean root target.
