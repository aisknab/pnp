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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-08-113` records 24,999 declarations,
13,376 theorems, 7,022 assumption-free theorems, 14,691 excluded private
declarations, 229 source-closure modules, and 2,364 reviewed milestone
candidates. Its 15,930,331 canonical bytes have SHA-256
`82fcdfd7443489f917d3987d31f604af6c163e9cb2a6fca2cd8aff98c38ff97f`.
The exact Lean source closure has SHA-256
`1ed937ea678bb853929da8c6958fe30fe09b837ad53fda5b53d5ce4da2584830`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-08-113` contains 93 milestones: 90
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,364 theorem types; its 766,476 bytes have SHA-256
`6d05c3a4d70ea78994a0302a60c8ba8381e37ff4e9c30a774ab474a13bb9baac`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-113`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-08-RESIDUAL-TERMINAL-FOUR-CORNER-SIDE-TIGHT-COMPLETION-112`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,916,515 bytes have SHA-256
`b9aff3d3eee8fed7d232c41cf0e81dc2355a3cd27a720b64aafde01746b20656`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-08-113` has a
199,054-byte TeX source with SHA-256
`73ef5719cc112e91e262b42846db82f4e92cd1dc1184484ad67f2b0b5006a01f`
and a deterministic 78-page, 438,997-byte A4 PDF with SHA-256
`e196ce1a2c373dbab4bf5e0e70418f0029beed4e1cfb959c78981c4880c6db02`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
