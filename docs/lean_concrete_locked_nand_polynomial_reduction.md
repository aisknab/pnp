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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-10-120` records 26,485 declarations,
13,860 theorems, 7,139 assumption-free theorems, 14,928 excluded private
declarations, 238 source-closure modules, and 2,468 reviewed milestone
candidates. Its 17,124,322 canonical bytes have SHA-256
`e69ac9c84dc15916632cc37b1d0e090d74d5057ce72160060ff8ed48b2623823`.
The exact Lean source closure has SHA-256
`3b31d12fbb322ffd5b93d1315bcff52fce916c120aed66c15c78eca3df983bf2`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-10-120` contains 100 milestones: 96
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,468 theorem types; its 800,452 bytes have SHA-256
`a36c1099429ae6d1b8d89cba1f40a2f71e3489d919d07770f6a3fca7624d23dc`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-10-120`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-10-FINITE-SATURATE-POSITIVE-119`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 2,013,081 bytes have SHA-256
`4fd7282f5f7455155f8ed5a86891488add6257f2c3f87f43258b70b04f4f2a6b`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-10-120` has a
207,974-byte TeX source with SHA-256
`df12f68f98ef0ffde0d3f6e92323a1071890e6db5c714cd08fd56192b6b3603b`
and a deterministic 81-page, 445,928-byte A4 PDF with SHA-256
`394e9f2403acc040b13d6bbe104ac0a3f7d55986fdf82cf7530daa93c9dd05c5`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
