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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-09-115` records 25,099 declarations,
13,423 theorems, 7,025 assumption-free theorems, 14,705 excluded private
declarations, 231 source-closure modules, and 2,397 reviewed milestone
candidates. Its 16,265,958 canonical bytes have SHA-256
`42695c4971028fff27f3c7f03eff1450c62845db0654436f59a190c3d2625af5`.
The exact Lean source closure has SHA-256
`01503dfe0db82b6672d8ace6cce5061846a8f0ad41322fc022f73676bad80124`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-09-115` contains 95 milestones: 92
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,397 theorem types; its 777,623 bytes have SHA-256
`9e688aae5553d680b6ff1f8fea8587f121edaf76c55efef110909f0d08173af8`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-09-115`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-09-RESIDUAL-TERMINAL-COMPUTED-BN2-SQUARE-LEGITIMACY-114`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,949,873 bytes have SHA-256
`c8adb9479ce14f702d693fc175710dd37670b0095c29d8522ced3ddb534bbeda`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-09-115` has a
201,436-byte TeX source with SHA-256
`391a179f9889bde11aef29b8e7bf7d32c4a7182d55a6bc556b3f80e7001cbc6d`
and a deterministic 79-page, 440,948-byte A4 PDF with SHA-256
`8bb12a7777ef0aad2af88a644e08877820bfb667da9636d8fa696f6fec31226e`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
