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

Current coordinates, counts, source and theorem fingerprints, byte sizes, and
report hashes are generated in the canonical publication artifacts rather
than duplicated here. The typed-restoration milestone contributes nine
reviewed theorem types. The current status remains fail-closed with all four
disclosed project assumptions, all five blockers, unset activation
fingerprints, and absent `PNP.Main.p_eq_np`.

## Deliberate nonclaims

The typed restoration operation and its coordinate-preservation theorem are
still explicit inputs. This milestone does not construct that operation from
a terminal candidate or establish its full semantic adequacy. It does not
connect complete restoration to a BN4 or BN5 contradiction, embed a local
route into the complete global outcome system, or prove global PkgC route
silence. It also does not prove full BN6 or Packet selector-realizer
completeness, polynomial generation or runtime, ZeroSlack or PCCMin, SAT in
P, removal of a project-specific assumption, or `P = NP`.
