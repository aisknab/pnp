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
`PNP-LEAN-THEOREM-INVENTORY-2026-08-05-104` records 24,260 declarations,
13,074 theorems, 6,927 assumption-free theorems, 14,574 excluded private
declarations, 220 source-closure modules, and 2,200 reviewed milestone
candidates. Its 14,200,832 canonical bytes have SHA-256
`fc56f19a06459903b4d234edb72133a398f6e1138230420e2de94f5adeaefcf6`.
The exact Lean source closure has SHA-256
`18d12d424a1f62f08dbd8ccd9fd96ea4ebd111276d28907c89e7f89a89e40efb`.

Publication-map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-05-104` contains 84 milestones: 81
earned and three deliberately unearned. The reduction milestone pins five
theorem types, while its audit covers nine reused interfaces and all seven
new public declarations. Of those 16 declarations, two have empty axiom
closure, two use only `propext`, and twelve use only `propext` and
`Quot.sound`. None reaches `Classical.choice` or a project axiom. The complete
map pins 2,200 theorem types; its 714,925 bytes have SHA-256
`11be1da6f2509275c140e6a86815b626f39661c57ec4d44428dd62ec08c69a75`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-05-104`, paired with public-surface
coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-05-RESIDUAL-TERMINAL-PROPER-POSITIVE-SUPPORT-SEARCH-103`,
records the exact function, output, language equivalence, reduction witness,
and recursive raw refinement as earned. Its 1,764,999 bytes have SHA-256
`5e261783dc48acfdf7f9b1a78291faa8be3e26ad8e85c188de77978b58184f17`.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-05-104` has a
188,927-byte TeX source with SHA-256
`719c9c79e2014b33843a86a665220dbea89146c15195c396be3d1cd918ff101c`
and a deterministic 74-page, 431,630-byte A4 PDF with SHA-256
`2e8d545dc874f8e2bdadb696c629f9d8a5a13516778eb315d61802bc34b68056`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` are retained.
