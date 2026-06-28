# No-hidden-oracle seed audit

This directory defines the current no-hidden-oracle coordinate:

```text
PNP-NO-HIDDEN-ORACLE-AUDIT-2026-06-27-01
```

The machine-readable manifest is:

```text
oracle-audit/NO_HIDDEN_ORACLE_AUDIT.json
```

Run it with:

```bash
npm run audit:no-hidden-oracle
```

The audit scans the configured repository source surface for executable SAT solvers, NP oracles, unbounded search, brute-force assignment search outside whitelisted small-model audits, and hidden minimum-equivalent-circuit calls.

The accepted result is a seed audit:

```text
noHiddenOracleAuditReady = true
fullNoHiddenOracleProved = false
```

The distinction matters. Formal references to oracle, minimization, brute-force SAT, or small-model exact search are allowed when they are documentation, checker metadata, or explicitly whitelisted executable audit code. Unwhitelisted executable calls are rejected.

The audit is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```
