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

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-12-133` records
27,794 declarations, 14,454 theorems, 7,347 assumption-free theorems, 15,008
excluded private declarations, 250 source-closure modules, and 2,589 reviewed
milestone candidates. Its 18,243,895 canonical bytes have SHA-256
`696c76220a092e5a84e7caa804fd1c57889f193968d1285b520c408f8237f5c1`;
the exact Lean source closure has SHA-256
`9b8afc2bac8c5f5b5fbe3c086f22602358c3f9b641aeb91e7de708f9f1001154`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-12-133`
contains 111 milestones: 109 earned and two deliberately unearned. It pins
2,589 theorem types; its 840,935 bytes have SHA-256
`a9f7ec898fb04e4842ea86281d2a6b257fc0c65dd422eb04a974bde169bf29d6`.
The typed-restoration milestone contributes nine reviewed theorem types.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-12-133` remains
fail-closed with all four disclosed project assumptions, all five blockers,
unset activation fingerprints, and absent `PNP.Main.p_eq_np`. Its 2,111,583
bytes have SHA-256
`6e7416a60485390b4414251c3b8f00214ed759f93d8091aef73cdb357da2dbfe`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-12-133` has a
223,061-byte TeX source with SHA-256
`2e42452a0d270c8e36cf7f381dbd38a64a535d07b8bc653e4e13ff526c574e7d`
and a deterministic 88-page, 460,049-byte A4 PDF with SHA-256
`5bca11cba837c8bdf90e27186974bf5398d4be78fae3360987afbf19746d271b`.

## Deliberate nonclaims

The typed restoration operation and its coordinate-preservation theorem are
still explicit inputs. This milestone does not construct that operation from
a terminal candidate or establish its full semantic adequacy. It does not
connect complete restoration to a BN4 or BN5 contradiction, embed a local
route into the complete global outcome system, or prove global PkgC route
silence. It also does not prove full BN6 or Packet selector-realizer
completeness, polynomial generation or runtime, ZeroSlack or PCCMin, SAT in
P, removal of a project-specific assumption, or `P = NP`.
