# Complexity implication ledger

This directory records the current complexity implication coordinate:

```text
PNP-COMPLEXITY-LEDGER-2026-06-27-01
```

The machine-readable ledger is:

```text
complexity/COMPLEXITY_LEDGER.json
```

Run the checker with:

```bash
npm run complexity:ledger
```

## Purpose

The ledger makes the final complexity implication explicit as proof objects rather than prose only:

```text
SAT is NP-complete
locked-NAND SAT threshold reduction is represented
residual-band minimization is conditionally polynomial
therefore SAT in P, if the conditional stack is fully discharged
SAT in P plus SAT NP-complete implies P = NP
```

The ledger is deliberately non-activating:

```text
complexityLedgerReady = true
fullComplexityImplicationDischarged = false
publicTheoremEmissionAllowedByLedger = false
```

## Proof-object chain

The current proof objects are:

```text
Complexity.BooleanCircuitSAT.NPComplete
Complexity.LockedNAND.SATThresholdReductionSeed
Complexity.ResidualBandMinimization.ConditionalPolynomial
Complexity.ConstructedSATAlgorithm.ConditionalPolynomial
Complexity.SATInP.ImpliesPEqualsNP
Complexity.PublicEmissionBoundary.NonActivation
```

Each object has a statement, status, proof rule, premise ids, evidence files, and machine-check status. The checker rejects missing premises, unknown evidence files, public theorem activation, premature full-discharge claims, and activated derived conclusions.

## Boundary

This ledger does not clear the current blockers:

```text
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

It also does not activate the final theorem:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
```

The historical proof report states the final theorem directly. This successor ledger records the implication route under the current public-review boundary so the chain can be checked and expanded before any public theorem-emission gate is reopened.
