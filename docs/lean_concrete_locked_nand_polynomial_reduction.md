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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-05-103` records 24,211 declarations,
13,049 theorems, 6,927 assumption-free theorems, 14,524 excluded private
declarations, 219 source-closure modules, and 2,183 reviewed milestone
candidates. Its 13,945,316 canonical bytes have SHA-256
`253dff68782561bf47e6a059233a3207aa73f5fab1e9dd05fc961af50f1912fb`.
The exact Lean source closure has SHA-256
`1dd96e3dacf0ce978270cdb494a25253a6d7f465eaa153937e8aaac06586983c`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-05-103` contains 83 milestones: 80
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,183 theorem types; its 709,628 bytes have SHA-256
`da4a437c935e7c5072b09534669305d6876ac7d9b375cef34a08d9dbb4390480`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-05-103`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-05-RESIDUAL-TERMINAL-SUPPORT-EXTRACTION-102`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,749,669 bytes have SHA-256
`0281e267926f6623d4cbb8f4e000a5c2ce4547602fa46bfcc40750903bfa9388`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-05-103` has a
187,652-byte TeX source with SHA-256
`50d1f6ea41f371510e0be86bd84dd33f535154228692dbe1ebcafb3ff5e47ca2`
and a deterministic 74-page, 430,495-byte A4 PDF with SHA-256
`a3db2479dbe5fe0620802bfdfcded79cbc1359ed62f65107b68e57e25fd897fa`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
