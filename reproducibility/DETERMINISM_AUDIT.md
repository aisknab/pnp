# Determinism audit

This directory records the current determinism-audit coordinate:

```text
PNP-DETERMINISM-AUDIT-2026-06-27-01
```

The machine-readable manifest is:

```text
reproducibility/DETERMINISM_AUDIT.json
```

The executable harness is:

```text
scripts/audit-determinism.mjs
```

Run the stronger default replay with:

```bash
node scripts/audit-determinism.mjs --json
```

By default, the audit runs this command twice:

```bash
node scripts/pnp-verify-all.mjs --json --skip-unit-tests --skip-release-audit
```

It compares:

```text
exitCode
stdoutSha256
stderrSha256
parsedJsonCanonicalSha256
stableArtifactDigestsBeforeAfter
generatedArtifactDigestsRun1Run2
```

## CI smoke mode

The CI workflow uses the same harness with a faster deterministic checker:

```bash
node scripts/audit-determinism.mjs \
  --json \
  --command "node pcc-complexity-ledger0.mjs --json" \
  --generated-artifact artifacts/complexity-ledger/latest-verdict.json
```

That verifies the determinism harness without recursively running the full repository verifier twice in every determinism workflow run. Independent reviewers can use the default command when they want the stronger replay.

## Boundary

The determinism audit is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

The CI smoke command does not claim full repository bit-for-bit determinism. It checks that the harness detects deterministic replay on a fast JSON-producing checker. The default command is stronger but still does not claim cross-platform byte identity across every environment.
