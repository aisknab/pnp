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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-10-122` records 26,540 declarations,
13,884 theorems, 7,159 assumption-free theorems, 14,935 excluded private
declarations, 240 source-closure modules, and 2,487 reviewed milestone
candidates. Its 17,207,898 canonical bytes have SHA-256
`f86ecb4b91dcc4bbd6988aba15b03dc5998a965dc21aabf830d40b41c871f434`.
The exact Lean source closure has SHA-256
`6adc25ee3d9920358ea8803adf47ab94d8e70c91026b8756bb45dbad1dda577d`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-10-122` contains 101 milestones: 99
earned and two deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,487 theorem types; its 805,053 bytes have SHA-256
`531a4dbd6d7925582aed1e6011d917e8dfdaf5576e1c259f63cd76a897d2aa5c`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-10-122`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 2,024,772 bytes have SHA-256
`cb5b4146385a6aa8d91fc1778007e7ea418a382237d5e706277c2d7a362172ac`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-10-122` has a
209,712-byte TeX source with SHA-256
`924606c880420091e8aff17f185ea52e8080c7729c3a1fba520f678e848be83a`
and a deterministic 82-page, 447,683-byte A4 PDF with SHA-256
`44d07e868371fedb86f48492f857a26d9a38b86b9b8e81a2ace8ba13c96eeafe`.

The concrete publication gate remains false. All four project assumptions,
all five blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
