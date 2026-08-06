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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-06-106` records 24,405 declarations,
13,134 theorems, 6,945 assumption-free theorems, 14,576 excluded private
declarations, 222 source-closure modules, and 2,240 reviewed milestone
candidates. Its 14,564,176 canonical bytes have SHA-256
`38c53b1e3e80059332ff62f135ffebcf04d6b5e39e158f0f48965295894c6e8d`.
The exact Lean source closure has SHA-256
`b4be2de72b2909cd9e47f0748e061f03041fbecbac1360e5797e89fef18404f6`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-06-106` contains 86 milestones: 83
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,240 theorem types; its 726,779 bytes have SHA-256
`3b27c4f934c3897bb71584846005e93a4816b63f4f8750a6884d18f1aedfe7ce`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-106`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-06-RESIDUAL-TERMINAL-GOVERNED-SUPPORT-COMPLETION-105`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,798,304 bytes have SHA-256
`5e6356f2b13da0161b4b0fb0ea299b504bfef54f7670f3a4371d1b19df26d10f`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-06-106` has a
191,295-byte TeX source with SHA-256
`1dc4a81c1f7a9805405019d1298f5324aaf39f599a4b58433bf72ceeb97a5a9c`
and a deterministic 75-page, 432,609-byte A4 PDF with SHA-256
`04683262a3cd12a893f7d1d67c750502f52f40a9c8bf7755912b3ebbff76d5fb`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
