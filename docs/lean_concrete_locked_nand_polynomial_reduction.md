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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-04-98` records 23,819 declarations,
12,894 theorems, 6,846 assumption-free theorems, 14,273 excluded private
declarations, 213 source-closure modules, and 2,127 reviewed milestone
candidates. Its 13,589,431 canonical bytes have SHA-256
`82d2b3ec7446b39e9387f8cd24c50e6e6123e4de78aa20c375dd7e34ca16643c`.
The exact Lean source closure has SHA-256
`d7b361d14706fa7194432f6e8510a20221ce1f2795064aea153171f19e31efa1`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-04-98` contains 78 milestones: 75
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,127 theorem types; its 692,946 bytes have SHA-256
`35f75fd42c70a29aedd19847abe43062cde26226884d8f25be0f2ccb91e50241`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-04-98`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-04-RESIDUAL-TERMINAL-MODE-FIREWALL-97`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,703,079 bytes have SHA-256
`adf99790bd0ae11074b379b54757af65fd2eb014cacaadc2d6cef43af53b8870`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-04-98` has a
182,263-byte TeX source with SHA-256
`1bb780ed9d8c80c906ca9631dd7d2f72a14ca2d1a73f1a773fafdaafea6b1e4f`
and a deterministic 71-page, 425,924-byte A4 PDF with SHA-256
`42ef88a63781e6e56fe43c99574926f85b67a30a524439c65b023f39e79570ef`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
