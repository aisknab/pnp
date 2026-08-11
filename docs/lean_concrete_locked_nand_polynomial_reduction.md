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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-11-128` records 27,442 declarations,
14,309 theorems, 7,290 assumption-free theorems, 14,999 excluded private
declarations, 246 source-closure modules, and 2,548 reviewed milestone
candidates. Its 17,726,895 canonical bytes have SHA-256
`612342db90e5887e2da6417963946437c82a14003f48deeddeae03d50caf637f`.
The exact Lean source closure has SHA-256
`4fde46c2f495422c43f5d2eb3ed80500c097a94b511aaecc74f5e8da979cd910`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-11-129` contains 107 milestones: 105
earned and two deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,548 theorem types; its 826,175 bytes have SHA-256
`9093dd1bdc84405be1748831ad59b98a60aabbd80d389f26f38f889de44770ea`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-129`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 2,076,560 bytes have SHA-256
`79c3ef6dace2f95cdad66add48c105e4ed5f95609b9c2819533685f63ed941aa`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-11-129` has a
217,706-byte TeX source with SHA-256
`e43ad410bc6e10f4e5d22d24c559b236e5698eb54b8b6b2659e2d0b3a8e4989c`
and a deterministic 85-page, 455,104-byte A4 PDF with SHA-256
`f48bc615866790d08151198272e89c9e68f8e1fd404ae46700ced768f42aa70c`.

The concrete publication gate remains false. All four project assumptions,
all five blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
