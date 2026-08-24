# Proof-bearing PCCMin normalization/oracle composition

M190 formalizes the manuscript's two-stage PCCMin iteration boundary:
`NormalizeOrGain` runs first, then the rank-ordered `PCCOracle` runs on the
normalized implementation. This is a composition theorem, not a construction
of either stage.

`PNP.DirectWire.PCCMinNormalizeOutcome current` has exactly two outcomes:

- a next implementation with a `StrictEquivalentGain` proof; or
- a `PCCMinNormalizedResult` that preserves complete Boolean semantics and
  cannot increase gate count.

There is no unresolved or unchecked-success outcome.
`PCCMinTotalNormalizer.normalize` is polymorphic over arbitrary finite
direct-wire input and output dimensions and every current implementation.

If the second-stage oracle finds a strict gain from the normalized result, the
checked non-increase and semantic equivalence lift it to a strict equivalent
gain from the implementation that entered normalization. Exact-minimum and
ZeroSlack oracle endpoints likewise transport back through normalization. A
ZeroSlack result makes the normalized result an exact minimum for the original
implementation; it does not incorrectly claim that the original implementation
itself was already minimum.

`composePCCMinNormalizerOracle` packages those branches as the M189 total-oracle
interface. `runPCCMinNormalizeOracleLoop` then reuses the existing well-founded
residual-slack recursion. The compiled endpoint
`PNP.DirectWire.pccmin_normalize_oracle_loop_checked_complete` proves that the
returned implementation:

- is semantically equivalent to the starting implementation;
- is globally semantically minimum;
- has the exhaustive reference-minimum gate count;
- has zero residual slack; and
- was reached through no more strict-gain iterations than the starting residual
  slack.

The regression fixtures use identity and exhaustive reference normalization
only to exercise every typed branch. They are not polynomial algorithms and do
not provide an active PCCMin implementation.

M190 does not construct or supply the `PCCMinTotalNormalizer` or
`PCCMinTotalOracle`, derive their terminal data, prove unconditional ZeroSlack,
encode either stage as a raw machine, or establish encoded-size polynomial
runtime or certificate bounds. It therefore does not close a fixed
risk-weighted checkpoint or a global gate. The proof-completion estimate remains
35 percent; formal artefact coverage changes independently to 166 of 168
current scoped rows.

## Verification

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPPCCMinNormalizeOracleCompositionAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPPCCMinNormalizeOracleComposition.lean
node --test audits/lean-pccmin-normalize-oracle-composition0.test.mjs
node scripts/export-lean-theorem-inventory.mjs --check
node scripts/generate-formal-publication.mjs --check
```

The fixed checkpoint definitions and unchanged score are recorded in
[`status/PROOF_PROGRESS.json`](../status/PROOF_PROGRESS.json).
