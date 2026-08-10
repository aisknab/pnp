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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-10-121` records 26,539 declarations,
13,883 theorems, 7,159 assumption-free theorems, 14,935 excluded private
declarations, 239 source-closure modules, and 2,486 reviewed milestone
candidates. Its 17,207,326 canonical bytes have SHA-256
`e48dcb80c3fde2a17ea39c5e6337a6e7f5a9988476330ee05e213185f89c7ab9`.
The exact Lean source closure has SHA-256
`d525c3be0e63e15f8a4336d785651f1d1fdef3dc867d2956302da34a947e85d6`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-10-121` contains 101 milestones: 98
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,486 theorem types; its 805,032 bytes have SHA-256
`f8fcc2a5cfde4e95bb74c41a5d57de5368b64baefc4891db11d74be403f52a38`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-10-121`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-10-RESIDUAL-RANK-WF-120`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 2,024,342 bytes have SHA-256
`14e653dd1cf68986b298983dec19988c8d6094228b0361d7312fc85166690477`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-10-121` has a
209,086-byte TeX source with SHA-256
`da46f3db65831263716f80e3ae075ef3110d5298f030a0f00f35c543fb714091`
and a deterministic 82-page, 446,880-byte A4 PDF with SHA-256
`96c11cddd00bec1547a337f7f9b004c926ed31c0ef5ae52715eff1270d54e822`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
