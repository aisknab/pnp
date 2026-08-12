# Finite PkgC typed restoration realization

This milestone strengthens the finite PkgC restoration branch in
`lean/PNP/ResidualTerminalPkgCTypedRestoration.lean`. The preceding classifier
retains exact coordinates only. The new theorem accepts a typed restoration
operation, materializes one full candidate for every quotient atom of the
canonical first separating pair, and proves complete exact-coordinate
multiplicity coverage.

## Earned scope

`TerminalPkgCTypedRestorer` separates three typed operations:

- the complete coordinate of a quotient atom;
- the full candidate that restores that atom; and
- the complete coordinate of the resulting full candidate.

The required proof says that restoration preserves the coordinate literally.
For a proof-bearing `TerminalPkgCSeparatingPair`, Lean then maps the left and
right consumer atoms through this operation in canonical list order. The
resulting full-candidate list has exactly the combined consumer length, and
its coordinate list is exactly the quotient coordinate list at every
position.

Two general multiplicity lemmas connect canonically indexed full units and
canonically indexed quotient shadows to the same unindexed coordinate count.
Consequently the typed realization supplies
`TerminalPkgCExactCoordinateCoverage`. A separate theorem proves that such
coverage contradicts any strict Hall deficit for the same equality-fibre
graph.

The total classifier has exactly two outcomes when a typed restorer is
available: the original scan proves V54 singletonization, or it returns the
first separating pair together with its materialized typed realization. No
third unclassified result is present.

## Verification

```text
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPkgCTypedRestorationAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPkgCTypedRestoration.lean
node --test audits/lean-residual-terminal-pkgc-typed-restoration0.test.mjs
```

The regression uses an arbitrary finite atom type and a distinct typed full
candidate carrying both its restored atom and a payload. It checks exact
candidate construction, positional coordinate preservation, complete
multiplicity coverage, incompatibility with a strict Hall deficit, and both
total classifier branches.

The hostile audit rejects assumptions, classical or unsafe shortcuts,
coordinate-only pseudo-candidates, arbitrary restoration lists, dropped
coordinate preservation, weakened multiplicity coverage, retained Hall
deficits, missing total branches, fixed carrier coordinates, and PkgC
overclaims.

## Mechanically generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-12-131` records
27,659 declarations, 14,395 theorems, 7,336 assumption-free theorems, 15,002
excluded private declarations, 248 source-closure modules, and 2,566 reviewed
milestone candidates. Its 17,830,363 canonical bytes have SHA-256
`7f21404feab8d7f354df31e904fda9a8f5fc9b64caefddf19398602166ca4cf9`;
the exact Lean source closure has SHA-256
`8bdc5a19e8a7360f6421b229858d95e6a430dece175bcc640b73041c4de768f6`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-12-131`
contains 109 milestones: 107 earned and two deliberately unearned. It pins
2,566 theorem types; its 832,573 bytes have SHA-256
`fd3d1ec5cc318aee5c0b9ec4b53f4a333385a9341dd2a545e568f088517a34f8`.
The typed-restoration milestone contributes nine reviewed theorem types.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-12-131` remains
fail-closed with all four disclosed project assumptions, all five blockers,
unset activation fingerprints, and absent `PNP.Main.p_eq_np`. Its 2,092,488
bytes have SHA-256
`f73285c1e43698ba0708b37d39a9ec6346d16f6dfcedbf875d227736e4c2eec4`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-12-131` has a
220,107-byte TeX source with SHA-256
`11e852d3d9049417f15824033595d560a145adcf62fea7e745d731c025afcfd6`
and a deterministic 87-page, 457,490-byte A4 PDF with SHA-256
`483c29088bc44f6c31d45b247545d88f2649b058d77f7e910409faa137166ca2`.

## Deliberate nonclaims

The typed restoration operation and its coordinate-preservation theorem are
still explicit inputs. This milestone does not construct that operation from
a terminal candidate or establish its full semantic adequacy. It does not
connect complete restoration to a BN4 or BN5 contradiction, embed a local
route into the complete global outcome system, or prove global PkgC route
silence. It also does not prove full BN6 or Packet selector-realizer
completeness, polynomial generation or runtime, ZeroSlack or PCCMin, SAT in
P, removal of a project-specific assumption, or `P = NP`.
