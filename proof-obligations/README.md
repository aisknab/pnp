# Proof obligation ledger

> **Superseded ledger:** This file describes the June 2026 assertion-checker obligation ledger. It is
> not the current formal proof inventory and does not establish any named mathematical proposition.
> See [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json)
> and [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

Historical coordinate:

```text
PNP-PROOF-OBLIGATION-LEDGER-2026-06-27-01
```

Machine-readable ledger:

```text
proof-obligations/OBLIGATION_LEDGER.json
```

Checker:

```bash
node pcc-proof-obligation-ledger0.mjs --json
```

The ledger records historical public-review obligations as machine-readable entries. Each entry
describes what a checker expected, not a formal derivation.

```text
id
statement
checker
sourceFiles
testFiles
status
dependencies
hashMode
```

The checker computes SHA256 digests of all declared source and test files at replay time. The ledger does not hard-code stale hashes as authority.

## Historical status classes

```text
machine-checked-seed
represented-not-activated
explicit-external-trust
blocked-release-obligation
```

The ledger is intentionally not a claim that every mathematical obligation has been fully discharged. It separates represented seed obligations, explicit trust-base obligations, and blocked release obligations.

## Historical boundary

The proof obligation ledger is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

The current reconstruction replaces this release-policy vocabulary with concrete Lean targets,
assumption auditing, executable definitions, and formal obligations listed in the authoritative status.
