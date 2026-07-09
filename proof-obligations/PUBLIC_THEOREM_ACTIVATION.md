# Public theorem activation withdrawal

Coordinate: `PNP-PUBLIC-THEOREM-ACTIVATION-WITHDRAWAL-2026-07-09-01`

The historical public-theorem activation is superseded. Current theorem emission is disabled:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
formalReleaseGatePassed = false
```

The historical activation depended on assertion-bearing JavaScript records and an abstract Lean bridge. Those artefacts remain available for provenance, regression testing, and reconstruction, but they are not mathematical theorem evidence.

A future activation can occur only after the formal release gate verifies a closed Lean root theorem with concrete machine and complexity semantics, no PNP-specific axioms or trust parameters, no placeholders, and formal correctness and polynomial-runtime proofs for the locked-NAND and residual-band route.

Human review is not a premise and is not required by this gate.

Run:

```bash
npm run proof:public-theorem-withdrawal
npm run proof:formal-reconstruction-status
```
