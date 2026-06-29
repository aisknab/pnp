# Artifact regeneration ledger

This directory records the current artifact-regeneration coordinate:

```text
PNP-REGENERATION-LEDGER-2026-06-27-01
```

The machine-readable source ledger is:

```text
artifacts/regeneration/REGENERATION_LEDGER.json
```

The audit writes its generated verdict here:

```text
artifacts/regeneration/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node scripts/audit-regeneration-ledger.mjs --json
```

The ledger records, for each public-review verification artifact:

```text
source files
regeneration command
output path
deterministic? flag
output committed? flag
generated at runtime? flag
```

Most verifier verdicts are intentionally runtime artifacts under `artifacts/**/latest-verdict.json`; they are regenerated from committed source manifests, checkers, and tests instead of being committed. Stable manifests, source ledgers, checkers, tests, and workflow definitions are committed and hashable.

## Boundary

The regeneration ledger is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
