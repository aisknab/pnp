# Concrete residual-band compatibility

M187 removes the report-facing residual-band language axiom without widening
the mathematical claim. `PNP.ResidualBandExactMinimization` is now the existing
concrete, fail-closed bitstring predicate
`PNP.Concrete.LockedNAND.EncodedDirectWireMinimumThreshold`.

For every intrinsically typed finite direct-wire candidate and natural
threshold, Lean proves that the canonical external encoding belongs to this
language exactly when

```text
threshold + 1 ≤ referenceMinimum candidate
```

The locked-NAND endpoint is definitionally the same predicate. Its reduction to
the residual-band endpoint is therefore the concrete identity polynomial
reduction, and `CheckerTrustModel` no longer accepts a caller-supplied
locked-to-residual reduction.

The compiled M187 endpoint is
`PNP.concrete_residual_band_compatibility_checked_complete`. Its axiom closure
uses only `propext`. At the M187 coordinate, the full conditional bridge still
depended on the two disclosed project axioms `PNP.GeneratePCCPack` and
`PNP.CheckPCCPackexp`; M188 subsequently replaces both with transparent typed
definitions without changing this milestone's claim.

## Claim boundary

`referenceMinimum` is an exhaustive finite semantic specification. This
milestone does not turn it into an executable polynomial minimizer, prove an
encoded-size residual-band promise, construct PCCMin, establish unconditional
ZeroSlack, put deterministic SAT in P, close a global gate, create
`PNP.Main.p_eq_np`, or prove `P = NP`.

The fixed checkpoint `axiom-remove-residual-band-minimum` is earned because the
compiled inventory now records `PNP.ResidualBandExactMinimization` as a
definition rather than project-specific proof authority. Risk-weighted proof
completion therefore moves from 32 to 33 percent, while formal artefact coverage
moves independently from 162/164 to 163/165. The uncertainty range remains 20
to 40 percent and all five global gates remain open.

## Verification

```bash
lake build PNP.ConcreteResidualBandCompatibility
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteResidualBandCompatibilityAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteResidualBandCompatibility.lean
node --test audits/lean-concrete-residual-band-compatibility0.test.mjs
```

The normal compiled-inventory, formal-publication, progress-ledger, generated
report, and complete repository validations remain required before publication.
