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

This closes the concrete polynomial-reduction packaging edge. It does not
identify the concrete target with the abstract `PNP.LockedNANDThreshold`
language, prove the report-level `PNP.Main.locked_nand_threshold`, establish
CNFSAT NP-hardness or membership in P, finish ZeroSlack/PCCMin, or prove
P = NP.

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
`PNP-LEAN-THEOREM-INVENTORY-2026-07-30-92` records 20,965 declarations,
11,430 theorems, 5,968 assumption-free theorems, 11,692 excluded private
declarations, 185 source-closure modules, and 2,035 reviewed milestone
candidates. Its 12,889,740 canonical bytes have SHA-256
`3413510e8712416cdb1b5d846053e5c886bbc1cd550fe7533411573e5f88bf64`.
The exact Lean source closure has SHA-256
`8f98bd81a6993bf025b232863107c1e71f932f509d6653cd92189acb6922958c`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-07-30-92` contains 72 milestones: 69
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,035 theorem types; its 666,185 bytes have SHA-256
`e9a0866b3d12afb6015be386250b02805fb0b5a772c1215e563ad4fe50e7117c`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-30-92`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-07-30-LOCKED-NAND-POLYNOMIAL-REDUCTION-91`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,634,055 bytes have SHA-256
`8bd1642ce803a8482921db9ae42ae623cc5cf760e4830050f9622624bce6ad51`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-30-92` has a
169,293-byte TeX source with SHA-256
`19c7dccef85be8c534821d7a8839fe27f6790bb3770dfa8e4749ff29ab52dcc7`
and a deterministic 66-page, 413,228-byte A4 PDF with SHA-256
`11473c09eaff4e1cb6f2f4d7a8c36441564376dab59904ceb10d76f011a2b7fa`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
