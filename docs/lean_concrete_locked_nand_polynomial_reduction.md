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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-12-132` records 27,734 declarations,
14,432 theorems, 7,342 assumption-free theorems, 15,005 excluded private
declarations, 249 source-closure modules, and 2,577 reviewed milestone
candidates. Its 17,980,963 canonical bytes have SHA-256
`ae56cd50f50e6b749e4af8b7d58d8db0790e2c09963ed86c5f507a5c36e7e366`.
The exact Lean source closure has SHA-256
`c038a1f4f3d8a95bbb3ff1914dbe5555a448c7b35f7e85a2c2b571b4ce1fb88b`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-12-132` contains 110 milestones: 107
earned and two deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,577 theorem types; its 836,589 bytes have SHA-256
`40178e6ea310301f0ff94fa6d97de759bd99d132509c79016fddb7fce2b99008`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-12-132`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 2,101,076 bytes have SHA-256
`ec7b7955471fc8af320d8751abd26b0338b59ca030b4d01a3a04dfff1db93f31`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-12-132` has a
221,513-byte TeX source with SHA-256
`df8ff9aa32c8edc76d9d8f5ba07fbb3bd80fa8435bd3cea28d572d7371cc8e59`
and a deterministic 87-page, 458,350-byte A4 PDF with SHA-256
`7c6fcf6a75ed8bb33527c334542fbf36ed0f64d2eacc79277a746d18184a2122`.

The concrete publication gate remains false. All four project assumptions,
all five blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
