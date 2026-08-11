# Concrete strict-v0 locked-NAND polynomial reduction

## What this milestone establishes

The legacy proof route converts a NAND satisfiability question into a
locked-NAND threshold question. Earlier milestones formalized the exact
strict-version-zero source language, the target encoding, the semantic
equivalence, a total source parser, and a literal target emitter.

This milestone packages those existing results as
`PNP.Concrete.PolynomialReduction`. Its source is `EncodedNANDSAT`, its target
is `EncodedLockedNANDThreshold`, and its function is the already-audited
`strictLockedNANDPolynomialTimeFunction`. For every input bitstring, the
function emits exactly `buildLockedNANDInstance`, and source membership is
equivalent to target membership of that output.

The reduction retains the recursive `FunctionProgram.RawRefinement` witness
for the strict parser/emitter composition. It therefore uses the concrete
finite charged-pipeline model rather than a caller certificate or host-side
schedule.

## Legacy anchor and strategic boundary

The construction follows the locked-NAND SAT embedding and locked-NAND
threshold route in the canonical legacy manuscript pinned by
`archive/legacy-v0/ARCHIVE.json`. Lean remains the theorem authority: the
legacy report supplies the intended construction and dependency order.

This closes the concrete polynomial-reduction packaging edge. The downstream
CNF-to-NAND milestone now identifies CNFSAT with `EncodedNANDSAT` through a
fixed finite machine, a polynomial-time function, and a direct polynomial
reduction, then composes that reduction with this one. This milestone does not
identify the concrete target with the
abstract `PNP.LockedNANDThreshold` language, prove the report-level
`PNP.Main.locked_nand_threshold`, establish CNFSAT NP-hardness or membership
in P, finish ZeroSlack/PCCMin, or prove P = NP.

## Public interface

The public module
`lean/PNP/Concrete/LockedNANDPolynomialReduction.lean` exposes:

- `strictLockedNANDPolynomialReduction`;
- exact function and output theorems;
- exact source/target language equivalence;
- `encodedNANDSAT_reducesTo_encodedLockedNANDThreshold`; and
- preservation of recursive raw refinement.

The focused verification commands are:

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteLockedNANDPolynomialReductionAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteLockedNANDPolynomialReduction.lean
node --test \
  audits/lean-concrete-locked-nand-polynomial-reduction0.test.mjs
```

## Mechanically generated publication evidence

Inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-08-11-126` records 27,193 declarations,
14,163 theorems, 7,264 assumption-free theorems, 14,995 excluded private
declarations, 244 source-closure modules, and 2,530 reviewed milestone
candidates. Its 17,583,178 canonical bytes have SHA-256
`884d84ade0af3ce3d588c6bba011fd21ec0fb7fdf0b0d1fee5d156f051002a8c`.
The exact Lean source closure has SHA-256
`a6aaa00d8faa48ed1d51bb0346363956d4cd2de8a14ecbe043458831d896dd02`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-11-127` contains 105 milestones: 102
earned and two deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,530 theorem types; its 820,122 bytes have SHA-256
`2935c7cb045d0f7ac2bb9baa98ffa7044543c410c84831fc9db36da66b47d157`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-127`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 2,060,926 bytes have SHA-256
`7b042bf47d86f20dbdb914d61c1ef84d39da0449692cde58cff223bcc50dcf3e`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-11-127` has a
215,538-byte TeX source with SHA-256
`2419f0f72282dc9c19762b0ee7a5ec438a6459901acc7d374ad9f42405921b6e`
and a deterministic 84-page, 453,006-byte A4 PDF with SHA-256
`438789317484ce2c73f194613f9906b9f3082b116d1129a0f97cdaf2330c321d`.

The concrete publication gate remains false. All four project assumptions,
all five blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
