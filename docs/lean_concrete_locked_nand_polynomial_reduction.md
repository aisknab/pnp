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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-07-110` records 24,675 declarations,
13,260 theorems, 6,984 assumption-free theorems, 14,607 excluded private
declarations, 226 source-closure modules, and 2,316 reviewed milestone
candidates. Its 15,168,239 canonical bytes have SHA-256
`2e585d493c1b5364f0bf340b7d141bbb231bef97d609056909f19481c77e45c9`.
The exact Lean source closure has SHA-256
`77155b9e3cd7ba5c931ccd20f587cb5aa0567e1b016b37845d904eec4205426d`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-07-110` contains 90 milestones: 87
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,316 theorem types; its 750,275 bytes have SHA-256
`20d29d0d85e4edd2ee0ab1cfbe41f403e17b2655ea82651ffeb089c0fe88372b`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-07-110`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-07-RESIDUAL-TERMINAL-FOUR-CORNER-CARRIER-109`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,867,836 bytes have SHA-256
`a411b2dae18d3869cea0ba236628604e9041f06010553d1e0cfc8b2434cef805`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-07-110` has a
195,614-byte TeX source with SHA-256
`51e174f1cbff5030a905ce6e791741a0f69facb1500acfad3b6b1c72ccdea641`
and a deterministic 77-page, 436,374-byte A4 PDF with SHA-256
`ed75cd52e1a5bb6a143838fa7a86f0d9a88ad66e9f1d039413fab5dc671690ad`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
