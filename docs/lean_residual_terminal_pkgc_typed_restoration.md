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

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-12-132` records
27,734 declarations, 14,432 theorems, 7,342 assumption-free theorems, 15,005
excluded private declarations, 249 source-closure modules, and 2,577 reviewed
milestone candidates. Its 17,980,963 canonical bytes have SHA-256
`ae56cd50f50e6b749e4af8b7d58d8db0790e2c09963ed86c5f507a5c36e7e366`;
the exact Lean source closure has SHA-256
`c038a1f4f3d8a95bbb3ff1914dbe5555a448c7b35f7e85a2c2b571b4ce1fb88b`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-12-132`
contains 110 milestones: 108 earned and two deliberately unearned. It pins
2,577 theorem types; its 836,589 bytes have SHA-256
`40178e6ea310301f0ff94fa6d97de759bd99d132509c79016fddb7fce2b99008`.
The typed-restoration milestone contributes nine reviewed theorem types.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-12-132` remains
fail-closed with all four disclosed project assumptions, all five blockers,
unset activation fingerprints, and absent `PNP.Main.p_eq_np`. Its 2,101,076
bytes have SHA-256
`ec7b7955471fc8af320d8751abd26b0338b59ca030b4d01a3a04dfff1db93f31`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-12-132` has a
221,513-byte TeX source with SHA-256
`df8ff9aa32c8edc76d9d8f5ba07fbb3bd80fa8435bd3cea28d572d7371cc8e59`
and a deterministic 87-page, 458,350-byte A4 PDF with SHA-256
`7c6fcf6a75ed8bb33527c334542fbf36ed0f64d2eacc79277a746d18184a2122`.

## Deliberate nonclaims

The typed restoration operation and its coordinate-preservation theorem are
still explicit inputs. This milestone does not construct that operation from
a terminal candidate or establish its full semantic adequacy. It does not
connect complete restoration to a BN4 or BN5 contradiction, embed a local
route into the complete global outcome system, or prove global PkgC route
silence. It also does not prove full BN6 or Packet selector-realizer
completeness, polynomial generation or runtime, ZeroSlack or PCCMin, SAT in
P, removal of a project-specific assumption, or `P = NP`.
