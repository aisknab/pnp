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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-09-117` records 25,571 declarations,
13,587 theorems, 7,043 assumption-free theorems, 14,779 excluded private
declarations, 233 source-closure modules, and 2,432 reviewed milestone
candidates. Its 16,710,476 canonical bytes have SHA-256
`2973e90172e160d070b3eb722ac146274c14e144b8c38677126149964c35dd28`.
The exact Lean source closure has SHA-256
`eec7fd5794e7fc945e4f3ef219b807cc3a6d5a0b07c67a2da5e33c07eda2ce0b`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-09-117` contains 97 milestones: 94
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,432 theorem types; its 788,580 bytes have SHA-256
`ab2fcbb854399694b0b8c80f3e752f46f272c86b351f37d6a5260d4afdde02cc`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-09-117`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-09-RESIDUAL-TERMINAL-SATURATION-POSITIVITY-FIREWALL-116`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,983,101 bytes have SHA-256
`148f927c21c7aada97a483658df7d287635cfacf7078ce51089fd859d5b0177a`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-09-117` has a
203,905-byte TeX source with SHA-256
`96a720e1e53d3a9d5facb2988c2f942bada036a9c11776a1a7ccbadb3a92b18e`
and a deterministic 80-page, 443,105-byte A4 PDF with SHA-256
`a6c28450e6110a29868f59100856a9598de90225b1d2631a13a900befe5e6429`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
