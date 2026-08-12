# Finite PkgC ambient BN4 ledger embedding

This milestone closes the next bounded gap above generated PkgC same-key
cancellation: it identifies that generated cancellation ledger with an exact
subledger of an explicit ambient BN4 problem, preserving order-independent
multiplicity rather than merely proving membership.

## Formal boundary

`ResidualTerminalPkgCAmbientBN4Ledger` works over arbitrary finite explicit
ledgers and arbitrary carrier types.  A
`TerminalPkgCAmbientBN4LedgerEmbedding` contains a `List.Perm` certificate that
the ambient ledger is exactly the generated opposite-sign cells followed by an
explicit remainder, up to order.  Consequently Lean proves:

- every generated cell occurs in the ambient ledger;
- the exact count of each cell is the generated count plus its remainder count;
- ambient length is the generated length plus the remainder length;
- positive and negative mass split across generated cells and remainder at
  every complete BN4 key;
- because the generated subledger is balanced, ambient signed mass and the
  executable residual signed contribution are exactly those of the remainder.

The canonical executable classifier accepts literal
`generatedCells ++ remainder` serialization and rejects inequality.  Other
orders remain admissible through an explicit kernel-checked permutation
certificate.  The classifier accepts no caller-provided success bit.

`TerminalPkgCComputedAmbientBN4Cancellation` also retains a successful
candidate-derived `TerminalComputedBN4ActivationCancellation`.  It proves every
embedded generated cell uses an atom from that kernel's canonical BN3 request
space.  If every separating pair has such an exact ambient binding and no
proof-bearing computed ambient cancellation exists, the earlier PkgC silence
theorem yields V54 singletonization.

## Deliberate non-claims

The ambient ledger, typed restorer, exact permutation certificate or canonical
serialization, and successful BN4 kernel are explicit proof-bearing inputs.
This milestone does not derive the ambient ledger or restorer from a terminal
candidate and does not prove the restorer's semantic adequacy.  It also does not
embed all local outcomes into a complete global route system, prove global PkgC
route silence, reconstruct the full historical PkgC/BN6/Packet path, establish
polynomial runtime, prove ZeroSlack or PCCMin, put SAT in P, remove a project
assumption, or prove P = NP.

## Evidence

The regression uses a four-atom finite consumer system.  Its separating pair
generates six balanced unit cells and an explicit positive-mass-five remainder,
so the ambient ledger has length seven, positive mass eight, negative mass
three, and signed mass five.  It exercises successful and rejected canonical
bindings plus the generic candidate-derived assembly boundary.

The hostile audit pins all 17 declarations, checks the exact axiom transcript,
rejects weakened membership-only embeddings, dropped remainders, altered mass
decompositions, erased candidate kernels, weakened completeness, assumptions,
and fixed carriers, and binds the published milestone to the compiled theorem
inventory.

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
This milestone contributes 12 reviewed theorem types.

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

```bash
lake build PNP.ResidualTerminalPkgCAmbientBN4Ledger
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPkgCAmbientBN4LedgerAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPkgCAmbientBN4Ledger.lean
node --test audits/lean-residual-terminal-pkgc-ambient-bn4-ledger0.test.mjs
```
