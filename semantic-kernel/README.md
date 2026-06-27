# Rule-family coverage ledger

This directory records the public self-verification rule-family coverage coordinate:

```text
PNP-RULE-FAMILY-COVERAGE-2026-06-27-01
```

The machine-readable ledger is:

```text
semantic-kernel/RULE_FAMILY_COVERAGE.json
```

Run its checker with:

```bash
npm run rule-family:coverage
```

The ledger currently covers seed evidence for these rule families:

```text
DPInd
GlobalFinalPrefix
SATReduction
Complexity
PublicEmission
SuccessorSeal
TrustBase
```

The coverage state is intentionally not a full historical proof-family coverage claim:

```text
coverageLedgerReady = true
fullRuleFamilyCoverageProved = false
```

Each family records positive, negative, and mutation counts plus evidence files. Later PRs should expand this ledger until every relevant checker and theorem-binding family has complete positive, negative, and mutation coverage.

The ledger preserves the public-review boundary:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
