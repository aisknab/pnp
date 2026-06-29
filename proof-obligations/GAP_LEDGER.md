# Gap ledger

Current coordinate:

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

The gap ledger records current unresolved, externally trusted, bounded-seed-only, and release-blocking items as explicit public-review obligations. It is deliberately blunt: every listed gap remains open until a later checker, release transition, or external-trust reduction pass closes it.

## Status classes

```text
blocked-release-gap
known-unresolved
represented-not-discharged
explicit-external-trust
bounded-seed-only
reproducibility-hardening-gap
```

## Current activation blockers

The current activation-blocking gaps preserve the existing release blockers:

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

The next hardening step should start converting the highest-priority activation-blocking gaps into dedicated checkers, beginning with finite-to-unbounded uniformity and unrestricted final soundness.
