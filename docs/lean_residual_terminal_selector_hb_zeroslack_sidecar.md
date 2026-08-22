# Proof-bearing Selector/HB ZeroSlack sidecar

`lean/PNP/ResidualTerminalSelectorHBZeroSlackSidecar.lean` replaces the
report-facing selector-silence and HB-closure string structures with one
checked, proof-bearing boundary.

The sidecar stores arbitrary finite typed data:

- a grouped BN6 family and its complete canonical handle universe;
- a typed-realizer table over those handles;
- a total exact-rank HN/BUD dependency table;
- the exact equation that the all-row selector-silence checker returned
  `true`; and
- the exact equation that the ranked no-outcome activity-closure checker
  returned `true`.

`selector_hb_zeroslack_sidecar_checked_complete` reflects those equations
through the existing strong finite-rank induction.  It proves that every
canonical selector is nonfaithful, every claim is exactly a typed bottom,
the complete HB closure proposition holds, every supplied HN/BUD activity bit
is false, and the dependency relation is well founded.  No caller Boolean,
string proof handle, or caller-supplied conclusion is accepted.

The evidence remains relative to supplied grouped-family, realizer,
environment, activity, dependency, and finite-rank tables.  The theorem does
not derive those tables from terminal data, prove selector faithfulness or
compatibility, establish blocker semantics or semantic dependency
completeness, connect selector silence to the BCEL contradiction, prove
unconditional ZeroSlack or PCCMin, establish polynomial size or runtime, put
SAT in P, remove a project assumption, or prove `P = NP`.

Review with:

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalSelectorHBZeroSlackSidecarAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalSelectorHBZeroSlackSidecar.lean
node --test audits/lean-residual-terminal-selector-hb-zeroslack-sidecar0.test.mjs
```
