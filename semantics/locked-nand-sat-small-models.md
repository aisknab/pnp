# Locked NAND SAT threshold small-model audit

This directory records the current locked-NAND SAT small-model coordinate:

```text
PNP-LOCKED-NAND-SAT-SMALL-MODELS-2026-06-27-01
```

The machine-readable configuration is:

```text
semantics/locked-nand-sat-small-models-config.json
```

The bounded reference audit is:

```text
semantics/locked-nand-sat-small-models.mjs
```

Run it with:

```bash
npm run semantics:locked-nand:sat-small-models
```

## Scope

The audit compares two independently computed predicates for a bounded CNF universe:

```text
brute-force CNF satisfiability
locked NAND final-output threshold predicate
```

The current formula universe covers unit clauses and single-variable contradiction pairs over at most two variables. The locked seed construction introduces a final lock `z` and builds a direct-wire NAND word whose final output is `z ∧ CNF`. Inside this seed universe:

```text
SAT      iff the final output is nonzero
SAT      iff exactMinimum(finalLockedOutput) > 0
UNSAT    iff the final output is identically zero
```

The exact minimum is computed by exhaustive search over generated NAND direct-wire words up to the configured small gate bound.

## Boundary

This is a bounded seed audit, not the full locked-NAND threshold theorem from the historical report:

```text
satSmallModelsReady = true
fullLockedNANDThresholdCoverageProved = false
```

Future PRs should expand this from unit/contradiction CNFs to clause-level macros, equality/constant/NAND trace macros, prefix conjunction, final-lock separation, and the full baseline threshold theorem.

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
