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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-07-109` records 24,583 declarations,
13,218 theorems, 6,971 assumption-free theorems, 14,595 excluded private
declarations, 225 source-closure modules, and 2,299 reviewed milestone
candidates. Its 15,014,491 canonical bytes have SHA-256
`d1743c46154588f40b4f04f5f1a0e02fdd043aa1b62c7f01e5c667d408357212`.
The exact Lean source closure has SHA-256
`c13bb497e99007317cf71871ac88dc94c21645caa70c82770690833f05a2494d`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-07-109` contains 89 milestones: 85
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,299 theorem types; its 744,575 bytes have SHA-256
`b628ea8684a56e748da90d753b054cce50428af9d213ff8928d0492b82f9cd1f`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-07-109`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-07-RESIDUAL-TERMINAL-SIDE-TIGHT-MINIMUM-108`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,849,193 bytes have SHA-256
`a29d10e7bc211b2c919910624557941898dc1f2888eb5cd6fc10ba00a6e89abb`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-07-109` has a
194,451-byte TeX source with SHA-256
`2c4421043189beee57aaf5d2bc6e14aa27584904739dadedbdb40fda4c88555c`
and a deterministic 76-page, 435,428-byte A4 PDF with SHA-256
`3495459a678fdf52d06553ffe2bff603438f037e282b8c257711eb855a0760b3`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
