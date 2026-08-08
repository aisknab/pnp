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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-08-114` records 25,059 declarations,
13,401 theorems, 7,025 assumption-free theorems, 14,705 excluded private
declarations, 230 source-closure modules, and 2,385 reviewed milestone
candidates. Its 16,124,474 canonical bytes have SHA-256
`fe036a74807d08c1e763a850722eb8113c1b3d186ef41d900641ed6e9eadb44c`.
The exact Lean source closure has SHA-256
`588c6626fcd4c0996f770b1118648ee99c82453ab303faf884e5e712d0107771`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-08-114` contains 94 milestones: 90
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,385 theorem types; its 773,039 bytes have SHA-256
`5ee8bb52412e04ce7b5ba9bccb619070d0963df00044f8f26b2bfe0aef73d186`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-114`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-08-RESIDUAL-TERMINAL-FOUR-CORNER-TIGHT-BASIS-MAXIMUM-113`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,935,171 bytes have SHA-256
`a72f8bfd4df79e29c1ea8908883f6211e65094ab162cf98b19a12b8ae080b158`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-08-114` has a
200,233-byte TeX source with SHA-256
`785181cde2595e9f21cb95239530b1aa9bc194b2e5d5d0198925956c8e853fd5`
and a deterministic 78-page, 439,981-byte A4 PDF with SHA-256
`447832f2f4992227446044f188aed18d07443dc0f9c285799f8eeeee8617d6e7`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
