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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-03-96` records 23,615 declarations,
12,830 theorems, 6,788 assumption-free theorems, 14,273 excluded private
declarations, 211 source-closure modules, and 2,103 reviewed milestone
candidates. Its 13,460,106 canonical bytes have SHA-256
`71165b553da0c375a19769cb9a7da02b20927d79cf47204d07e86ae14533c5fe`.
The exact Lean source closure has SHA-256
`23ebbd4f1251d92adb3c0a1d60cf63b52683a41f39a84375c87b0781d2f522ac`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-03-96` contains 76 milestones: 73
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,103 theorem types; its 685,582 bytes have SHA-256
`69e15a77f4df72b6a0c3e1c2dce69cb9f156344d8b432524a0ab954106aaa27d`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-03-96`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-03-RESIDUAL-GAIN-STOPPING-SPECIFICATION-95`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,684,244 bytes have SHA-256
`251b3b184c7195f8a951d474701610a3650a2d42d98193ebb515cbcb16c4597f`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-03-96` has a
179,212-byte TeX source with SHA-256
`824cc9ee94e1b4598fba805eaea52b246cc471a3a2644a5faf295a392dfb25d9`
and a deterministic 70-page, 422,655-byte A4 PDF with SHA-256
`c177248af36860a452cc4b5683fea11c9e3ba1de0e2d1830e9cb7b51a7bc36d7`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
