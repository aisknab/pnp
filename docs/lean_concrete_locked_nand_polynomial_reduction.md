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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-06-105` records 24,337 declarations,
13,104 theorems, 6,937 assumption-free theorems, 14,575 excluded private
declarations, 221 source-closure modules, and 2,219 reviewed milestone
candidates. Its 14,403,337 canonical bytes have SHA-256
`7712cae2dd53ef95a9ec7e10ea89ff29681101268a92c06d21a94be5efc02b32`.
The exact Lean source closure has SHA-256
`0e4bb045091e6b4c53181698b4c43f97f7cfe1c0081a8895e572d9035ff454dd`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-06-105` contains 85 milestones: 81
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,219 theorem types; its 720,540 bytes have SHA-256
`1ed4556de466e6a4d079bee37479c6ca3e2d9c7a26dcd256d2cb02fa8ca482c6`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-105`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-06-RESIDUAL-TERMINAL-SATURATED-SUPPORT-SQUARE-CLOSURE-104`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,780,999 bytes have SHA-256
`ba386511f193e7f0b18714773e84a91e591c32a91adda70810fa24d6d634a2ec`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-06-105` has a
190,115-byte TeX source with SHA-256
`f151378f77052be84f05edea03b8a0052e1955aebff4b3afa1964aca8937961d`
and a deterministic 75-page, 432,278-byte A4 PDF with SHA-256
`39556a8d59f7dfe9407cfa4d49a7ddf388e4e9f456c3562eb76d672523461505`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
