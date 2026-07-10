# Complexity implication ledger

> **Superseded complexity ledger:** This June 2026 ledger is historical assertion-checker evidence.
> It does not supply the concrete complexity model, runtime proof, or root theorem required by the
> current formal reconstruction. See
> [`../status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json) and
> [`../docs/FORMAL_RECONSTRUCTION.md`](../docs/FORMAL_RECONSTRUCTION.md).

This directory records the historical complexity implication coordinate:

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

The ledger represented the final complexity implication as historical checker objects rather than
prose only:

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

The historically recorded proof objects are:

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

This ledger did not clear the historical release-policy blockers:

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

The historical proof report stated the final theorem directly. This successor ledger recorded an
implication route under the old public-review boundary. It is not a current proof inventory or a
basis for reopening theorem emission.
