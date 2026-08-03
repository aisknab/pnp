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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-03-95` records 23,601 declarations,
12,818 theorems, 6,776 assumption-free theorems, 14,273 excluded private
declarations, 210 source-closure modules, and 2,093 reviewed milestone
candidates. Its 13,432,952 canonical bytes have SHA-256
`26fdb6098e7169b2ba8fbbfd6554370e820ee9598709d484138eecea53f4450b`.
The exact Lean source closure has SHA-256
`3430306ac20401ae6967122be54eab38adeb843595f83049e97c09397eeb468b`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-03-95` contains 75 milestones: 71
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,093 theorem types; its 682,067 bytes have SHA-256
`66f06c9891f0f60236ba2742f5965ac94813bb08b4cf722ff021ac8a37ea9fb1`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-03-95`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-03-RESIDUAL-GAIN-CHAIN-BOUND-94`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,675,872 bytes have SHA-256
`94aef5e267925651eed37adaacf3a767b103f9e0943eed50e3e0a677c5751076`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-03-95` has a
177,190-byte TeX source with SHA-256
`b13f970372569e2559a0c2f60188420210ffccdc9653e5ee04f36cf57d6ce835`
and a deterministic 69-page, 420,680-byte A4 PDF with SHA-256
`a0dfe6b1fcbe0769f612bb494b610ee4727ef7e37cd6f0156f72d2e990a019ac`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
