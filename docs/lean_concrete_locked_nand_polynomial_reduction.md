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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-04-100` records 23,884 declarations,
12,925 theorems, 6,851 assumption-free theorems, 14,317 excluded private
declarations, 215 source-closure modules, and 2,145 reviewed milestone
candidates. Its 13,702,270 canonical bytes have SHA-256
`6807fe409ff302b55bffe69f3f7a13c4f0692c297504c9a9ab50692dc57e601e`.
The exact Lean source closure has SHA-256
`6a6617e881fca16a46ac1fcb3c5f0968e35cee759596bdbb537d098c6ba24e10`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-04-100` contains 80 milestones: 77
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,145 theorem types; its 698,849 bytes have SHA-256
`258f841262220fb0d78db65d35a99809ac2898aed961ba7593dfeadccb6fda54`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-04-100`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-04-RESIDUAL-TERMINAL-PROJECTION-TRANSFER-99`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,718,803 bytes have SHA-256
`fa627d391af8be33015576f7b091c32d184cfebe25c708df38f0c6207a313b50`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-04-100` has a
184,334-byte TeX source with SHA-256
`4b1f709d9bc591832962253a3bc52bec0d8548ea0b0da4a745f4602d04c27aae`
and a deterministic 72-page, 427,894-byte A4 PDF with SHA-256
`da6c2ef9919aef7901253e477a3889808bc6496a79966566e7831bafda5d1b2f`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
