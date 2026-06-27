# Checker totality seed audit

This directory defines the current checker-totality audit coordinate:

```text
PNP-CHECKER-TOTALITY-AUDIT-2026-06-27-01
```

The manifest is:

```text
checker-totality/CHECKER_TOTALITY_AUDIT.json
```

The audit has two parts:

1. Inventory every exported `Check*0` function found in repository `.mjs` files.
2. Fuzz the current public self-verification checker surface with valid and malformed inputs and require every invocation to return an `accept` or `reject` record without throwing.

The seed audit is intentionally honest:

```text
checkerTotalitySeedReady = true
fullCheckerTotalityProved = false
```

It does not claim that every historical checker is total yet. It creates the executable inventory and a checked seed set so later PRs can expand the audited surface until the full inventory is covered.

Run it with:

```bash
npm run checker:totality
```

The audit preserves the public-review boundary:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
