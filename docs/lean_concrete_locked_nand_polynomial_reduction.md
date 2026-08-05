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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-05-102` records 24,150 declarations,
13,019 theorems, 6,918 assumption-free theorems, 14,409 excluded private
declarations, 218 source-closure modules, and 2,166 reviewed milestone
candidates. Its 13,833,685 canonical bytes have SHA-256
`869875ff563e3aedad0f2b24d241ff91c7c6eb3f35b4ac655346b6f237041188`.
The exact Lean source closure has SHA-256
`dd6fd7a05cce2c156ce9196a3c60814a9a220d3d8d0e753e2bcd75d184b2184b`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-05-102` contains 81 milestones: 77
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,166 theorem types; its 704,920 bytes have SHA-256
`89fbdf1ba505549c8f2f0db99bdc4b6a53895c2a65b094415c7d03dfb0601c4c`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-05-102`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-05-RESIDUAL-TERMINAL-PHYSICAL-SUPPORT-COMPLETION-101`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,735,904 bytes have SHA-256
`4afb84f20713eec92dce2c9c9a0dcaa2f986e893d527d5e1932c41377c73bdc9`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-05-102` has a
186,475-byte TeX source with SHA-256
`5cc640d457bd64d61c842c2b89bd164052b7cd5a4b123409d821018fac46b396`
and a deterministic 73-page, 429,037-byte A4 PDF with SHA-256
`d4aceaca58c7554027b1c9424da90548c1310dacec77d4074861569b32298938`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
