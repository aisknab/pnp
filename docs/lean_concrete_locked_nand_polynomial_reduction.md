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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-11-125` records 27,129 declarations,
14,125 theorems, 7,249 assumption-free theorems, 14,995 excluded private
declarations, 243 source-closure modules, and 2,523 reviewed milestone
candidates. Its 17,551,864 canonical bytes have SHA-256
`fbd4614c550813bc8deff259f9442b37336efb40be3835e07880842c8e8a3be7`.
The exact Lean source closure has SHA-256
`c939e940c892279b3845b2d30dc0baa724d53b6f9a6249ccfa2900c7c00cb00f`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-11-126` contains 104 milestones: 102
earned and two deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,523 theorem types; its 817,481 bytes have SHA-256
`c4c3f6234e7bf80626d9e271991cea7ffdf00fe90c49c805c42e4a00628e59a3`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-126`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-10-CONCRETE-LOCKED-NAND-THRESHOLD-121`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 2,054,365 bytes have SHA-256
`1e02d5abeb1d1b3138e8b59c4926a037c7653617720eb85a1efc25a1bb487cc8`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-11-126` has a
214,459-byte TeX source with SHA-256
`348ebff0df6ed0ce7eb27f1a529af88139a8dde58b13aad29433b9096ff321e3`
and a deterministic 84-page, 452,029-byte A4 PDF with SHA-256
`14f64fd605590edcb64d38314595db082b4916806c5ae3712977c7ab6cc47610`.

The concrete publication gate remains false. All four project assumptions,
all five blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
