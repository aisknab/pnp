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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-04-99` records 23,855 declarations,
12,917 theorems, 6,849 assumption-free theorems, 14,316 excluded private
declarations, 214 source-closure modules, and 2,141 reviewed milestone
candidates. Its 13,657,794 canonical bytes have SHA-256
`7c3daaa3cbf191508d48054ecf1d1b48cfbd7601d5e3756fa9d057db383c6121`.
The exact Lean source closure has SHA-256
`7a2758acc431c096d32534b9b0860fdf996b27a5f3def918e131dd10c1b99006`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-04-99` contains 79 milestones: 76
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,141 theorem types; its 696,977 bytes have SHA-256
`9851bbb8e0cecbf94bd88e79c18b1713fb9803db838cbe1ffdb0564f35f40103`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-04-99`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-04-RESIDUAL-TERMINAL-PROJECTION-MINIMUM-98`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,713,784 bytes have SHA-256
`81a55d765359ea8131eba15a94ad1cddd4edc90b8bfafb358dc45e5260fdafc2`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-04-99` has a
183,404-byte TeX source with SHA-256
`8af67370cfd1b95708f30da4009dfdb04f5ab8793db81ae1987c411982f1b869`
and a deterministic 72-page, 427,318-byte A4 PDF with SHA-256
`cd354d1406f9cfa3374ebf716cfc401261bb9905bc573fc3c0d6368e7ca1f0ad`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
