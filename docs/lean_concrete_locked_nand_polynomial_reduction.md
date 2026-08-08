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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-08-112` records 24,934 declarations,
13,352 theorems, 7,015 assumption-free theorems, 14,691 excluded private
declarations, 228 source-closure modules, and 2,352 reviewed milestone
candidates. Its 15,824,195 canonical bytes have SHA-256
`10ca3467d9c899300ac9c76c84ce62f87c8157e73fc39f8af82b203a4be9a8eb`.
The exact Lean source closure has SHA-256
`3161b45bbf5468a66e86fac1cf8dd6bef3ea19b1d472c536a620695085e589d1`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-08-112` contains 92 milestones: 88
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,352 theorem types; its 761,711 bytes have SHA-256
`8404f2c2b178d87c42f4501b4490286c90da593281dad2708297c22b0fbfa9df`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-112`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-08-RESIDUAL-TERMINAL-FOUR-CORNER-OPTIMUM-COHERENCE-111`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,901,511 bytes have SHA-256
`e0515fe3af9c24f155165f172f2f00c1bbcff21822b5479141183262cf34b8d5`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-08-112` has a
197,818-byte TeX source with SHA-256
`550fa4769b476b52cae5df3efa912a925b9e4c6d1460fe6a601d060e4a810f72`
and a deterministic 77-page, 437,284-byte A4 PDF with SHA-256
`0e30911e395f6054e968b2ac0de1a27cf9bb2e77a182e6744ac37407dd1de058`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
