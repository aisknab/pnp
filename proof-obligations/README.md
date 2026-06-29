# Proof obligation ledger

Current coordinate:

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

The ledger records the current public-review theorem obligations as explicit machine-readable entries. Each obligation includes:

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

## Current status classes

```text
machine-checked-seed
represented-not-activated
explicit-external-trust
blocked-release-obligation
```

The ledger is intentionally not a claim that every mathematical obligation has been fully discharged. It separates represented seed obligations, explicit trust-base obligations, and blocked release obligations.

## Boundary

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

The next hardening pass should expand this ledger into a gap ledger and then eliminate or downgrade each gap through executable proof objects, independent verifiers, or formal external-theorem references.
