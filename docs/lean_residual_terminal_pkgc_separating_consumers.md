# Finite PkgC separating-consumer restoration dichotomy

This milestone reconstructs a bounded finite edge of the pinned manuscript's
PkgC separating-consumer argument. It sits between the BN5 exact-coordinate
shadow classifier and V54's singletonization premise. The Lean module is
`lean/PNP/ResidualTerminalPkgCSeparatingConsumers.lean`.

## Earned scope

For an arbitrary finite `TerminalV54ConsumerSystem`, Lean enumerates all
ordered pairs of listed minimal consumers and selects the first disjoint pair
that is not singleton-singleton. The scan is executable and proof-bearing. If
the scan finds no pair, Lean proves exactly
`DisjointPairsSingletonized`, the premise consumed by V54.

For a found pair, the module generates canonical quotient units from every
atom of the two consumers. A caller supplies only the atom-to-coordinate map
and the finite list of full-restoration coordinates. The existing BN5 matcher
then classifies that explicit universe into one of two proof-bearing results:

- complete multiplicity coverage in every exact-coordinate fibre; or
- a strict Hall deficit whose quotient neighborhood is smaller than its full
  subset and which deterministically emits the named local Q restoration
  route.

Every matching edge is literal equality of the complete coordinate. When the
coordinate is `TerminalBN5ShadowCoordinate`, this preserves the nested BN4
activation key together with frontier, charge-owner, obligation,
origin-kernel, and mode-projection data. The quotient-unit list is proved to
have exactly the combined consumer length and to be nonempty.

The total theorem has no fourth result: the system is already singletonized,
the first separating pair has complete exact-coordinate coverage, or that
pair has a proof-bearing strict Hall deficit.

## Verification

The regression covers all three total branches. It checks deterministic first
pair selection, canonical quotient coordinates, complete coverage, a hostile
missing coordinate that forces the strict Hall route, and the exact V54
singletonization conclusion when no separating pair exists.

```text
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPkgCSeparatingConsumersAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPkgCSeparatingConsumers.lean
node --test audits/lean-residual-terminal-pkgc-separating-consumers0.test.mjs
```

The 27-declaration axiom transcript permits only the Lean standard axioms
`propext` and `Quot.sound`. The hostile source audit rejects assumptions,
classical or unsafe shortcuts, a weakened separating-pair scan, caller-supplied
quotient units, coordinate-changing edges, non-strict Hall localization,
missing total branches, fixed carrier coordinates, and PkgC overclaims.

## Mechanically generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-12-129` records
27,573 declarations, 14,360 theorems, 7,314 assumption-free theorems, 15,002
excluded private declarations, 247 source-closure modules, and 2,557 reviewed
milestone candidates. Its 17,787,380 canonical bytes have SHA-256
`859ef0595f1eeea872518b0f399a788225e3a2ed9fefe987c6ae5bd6b3783aaf`;
the exact Lean source closure has SHA-256
`4608b17afe6e8d0be3f7f6e0fae526025c0050f64dca9670e71ae89f9f27aa7c`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-12-130`
contains 108 milestones: 106 earned and two deliberately unearned. It pins
2,557 theorem types; its 829,327 bytes have SHA-256
`f076b8f813c2877d7a03b7090151d4c9db9f4793a5c4f40fbdc5125c82808ed8`.
The PkgC restoration milestone contributes nine reviewed theorem types.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-12-130` remains
fail-closed with all four disclosed project assumptions, all five blockers,
unset activation fingerprints, and absent `PNP.Main.p_eq_np`. Its 2,084,476
bytes have SHA-256
`1a4609a63dd44da92cfc4558d1cef0db60430b26942cc6b3e2d199eb35d66ed9`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-12-130` has a
218,897-byte TeX source with SHA-256
`2f3aeaa0801283edbcb713f74567d133ea4598e3b5eb04541ac083d31fbf7546`
and a deterministic 85-page, 455,853-byte A4 PDF with SHA-256
`fedbffc7877c0cf4da70f6eea77395f7ee413e48917a80ee3ea5f24d9c325fec`.

## Deliberate nonclaims

The restoration coordinate universe remains explicit. This theorem does not
establish the full historical PkgC theorem. It does not derive consumers or
restorations from a terminal candidate, connect complete coverage back to a
BN4 or BN5 contradiction, embed the Hall route into the complete global
outcome system, or prove global route silence. It does not prove full BN6 or
Packet selector-realizer completeness, polynomial generation or runtime,
ZeroSlack or PCCMin, SAT in P, removal of a project-specific axiom, or
`P = NP`.
