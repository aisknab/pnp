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
`PNP-LEAN-THEOREM-INVENTORY-2026-07-31-94` records 23,575 declarations,
12,806 theorems, 6,767 assumption-free theorems, 14,273 excluded private
declarations, 208 source-closure modules, and 2,081 reviewed milestone
candidates. Its 13,380,071 canonical bytes have SHA-256
`f6dc633360d0aad4df37e2273c7304723d5187a66c67a88e1416e4adbf7e62ca`.
The exact Lean source closure has SHA-256
`72c9997c0ce9aa5a748abb273b49871f3583ad6c9ad8d8d1b7ae1e96ee9538f1`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-07-31-94` contains 74 milestones: 71
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,081 theorem types; its 678,310 bytes have SHA-256
`3743f38dd65073bf0e57d4525d4989dda530676a74bd61a5d7caf0cb7b616aa5`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-31-94`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-07-31-CNF-TO-NAND-POLYNOMIAL-REDUCTION-93`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,665,641 bytes have SHA-256
`feaf6bca770c3e4e71b1fee10b60ce0e9ca7321a1a5b81da45b013184c1d0fa3`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-31-94` has a
175,276-byte TeX source with SHA-256
`2c6283ed6f6f54fc442e75b795afb389521fa9f3fa3a27ddf9adfa80e8f18483`
and a deterministic 68-page, 419,182-byte A4 PDF with SHA-256
`6a3823fd204005cbed79b487a4b90d1567b14f359529dcb0a037e4e81d3972cc`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
