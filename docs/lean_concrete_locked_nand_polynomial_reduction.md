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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-10-119` records 26,087 declarations,
13,740 theorems, 7,102 assumption-free theorems, 14,908 excluded private
declarations, 236 source-closure modules, and 2,459 reviewed milestone
candidates. Its 17,006,508 canonical bytes have SHA-256
`1901e247b93dcfedd06dc09be1ba6ded421ba422baa011a4cf4f9806846ef757`.
The exact Lean source closure has SHA-256
`a7ba81b064643e574a6a5084e4947a61db2fc19528155cf2b11cf37f67f40682`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-10-119` contains 99 milestones: 96
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,459 theorem types; its 797,067 bytes have SHA-256
`410dc11e15005c24df28c455d3d0e1d96926f2dcffd6c080e45c60a395422849`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-10-119`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-10-INTERFACE-EXPOSURE-ROUTING-118`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 2,004,368 bytes have SHA-256
`03fb380c7b0d1a5ed1521d0fe5c06bbe99d34507af56561a5bfdfa85d0839a5e`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-10-119` has a
206,457-byte TeX source with SHA-256
`9293f165e378e9d196e7725a8a895f7a2d4c09b543ba3143ba7d34055b2d236a`
and a deterministic 81-page, 444,907-byte A4 PDF with SHA-256
`e534cfce77a5f849f21af91942a96ce832160a65b42cdb52c15c4df0e8946f74`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
