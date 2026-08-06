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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-06-108` records 24,485 declarations,
13,183 theorems, 6,956 assumption-free theorems, 14,594 excluded private
declarations, 224 source-closure modules, and 2,279 reviewed milestone
candidates. Its 14,930,297 canonical bytes have SHA-256
`17abf9c431e40fc2775fde868ff9312acf8db37907aa4a5ca64d5aa5c41e75d0`.
The exact Lean source closure has SHA-256
`54ced1d99c5c88c2580956e2b065101f45cbaef8c41de40f0996a3bf74ca0d3a`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-06-108` contains 88 milestones: 85
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,279 theorem types; its 738,472 bytes have SHA-256
`4b1ba7361fbb2dbbd103a14d848248d1729ad2305a86746021955c183ddc7ccb`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-108`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-06-RESIDUAL-TERMINAL-PROJECTION-SQUARE-107`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,832,643 bytes have SHA-256
`8e7e4c01da163413c95ca7bf3b096754bf88b8748f782c72d59ed96c0f7fde6f`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-06-108` has a
193,376-byte TeX source with SHA-256
`422b680daefa772e192eb47fa6fbb826e890b35563a94e05d0bca32da8ad82db`
and a deterministic 76-page, 434,491-byte A4 PDF with SHA-256
`edf229a4f5e7c6006fed6bb93774a6ba82de413f288cb6cb0ea5f189aa91d36d`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
