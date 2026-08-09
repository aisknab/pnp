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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-09-116` records 25,515 declarations,
13,564 theorems, 7,043 assumption-free theorems, 14,779 excluded private
declarations, 232 source-closure modules, and 2,426 reviewed milestone
candidates. Its 16,596,402 canonical bytes have SHA-256
`efb6c71dcef5ac3396058e8930785aef0b11d28c28d1db2dd0fc3234547e82f6`.
The exact Lean source closure has SHA-256
`1f466ddd7a7436ab57ddfbccce989d01c4d8e61e90480d76f6265e82c0fdd228`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-09-116` contains 96 milestones: 93
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,426 theorem types; its 785,551 bytes have SHA-256
`24c3ad1302faa4e5e375911eaaebe7b3b42ef4fbd9ee3b6e1bf5ebdd5d7d4bff`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-09-116`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-09-RESIDUAL-TERMINAL-COMPUTED-BCEL-ANCHOR-NUCLEUS-115`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,973,518 bytes have SHA-256
`454bafaa83b7c4351a73bcc6f69e00f77270272da362216323f64ae50c290345`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-09-116` has a
202,712-byte TeX source with SHA-256
`202bb30ae62cca0fde0d1f73e8618b921ca1abd93bca5db71299b3568cd5143a`
and a deterministic 79-page, 441,656-byte A4 PDF with SHA-256
`84d07af20399c072ccc950f40d6403bc1985ff5aeff27ec6f13deef544764b91`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
