# Finite PkgC typed restoration same-key cancellation

## Legacy anchor and dependency edge

The pinned legacy manuscript's Section 11.5, “Package C, renamed PkgC:
separating consumers,” says that a nonsingleton disjoint pair of active minimal
consumers is expanded into full-restoration candidates. A complete match is
then supposed to produce same-key cancellation or full-shadow localization;
when every named outcome is absent, only singleton-singleton disjoint pairs
remain and V54 applies.

The preceding Lean milestone stopped one edge earlier. It accepted an explicit
typed coordinate-preserving restorer, materialized one full candidate per
participating quotient atom, and proved exact BN5-coordinate multiplicity
coverage. It did not turn those matched values into the BN4 cancellation
object used by the manuscript's next sentence.

## Unbounded abstraction

`ResidualTerminalPkgCSameKeyCancellation` works over arbitrary types and an
arbitrary finite `TerminalV54ConsumerSystem`; there is no fixed carrier size or
hard-coded cut coordinate. Its restorer's coordinate is the complete
`TerminalBN5ShadowCoordinate`, whose `key` field is the nested
`TerminalBN4ActivationKey`.

For each quotient atom the construction emits exactly two unit cells:

1. a positive cell at the quotient coordinate's BN4 key; and
2. a negative cell at the restored full candidate's BN4 key.

The restorer's already-required equality of complete BN5 coordinates implies
equality of those nested BN4 keys. Concatenating the pairs over any finite atom
list therefore gives equal positive and negative multiplicity at every key.
The existing executable BN4 classifier consequently returns an empty residual
list, and the signed integer mass is zero, at every key.

For the canonical first separating pair, the proof-bearing
`TerminalPkgCSameKeyCancellationRealization` retains both the prior typed
candidate realization and this mechanically generated ledger. The theorem
`terminalPkgC_typedRestoration_sameKeyCancellation` returns either V54
singletonization or such a realization. The adjacent theorem
`terminalPkgC_sameKeyCancellation_silence_singletonizes` expresses the
manuscript's local no-outcome implication: if every proof-bearing generated
cancellation is excluded, no nonsingleton disjoint pair remains.

## Checked boundary

The axiom transcript covers every declaration in the new module. The
regression uses three participating atoms with distinct outer BN5 payloads but
one shared nested BN4 key; it checks six generated cells, mass `3 = 3`, empty
residual, zero signed mass, both classifier branches, and the silence-to-
singletonization theorem. The hostile source audit rejects changed signs,
non-unit mass, omission of either consumer, a caller-supplied cell ledger,
weakened key projection, positive/negative imbalance, loss of the executable
BN4 classifier, a positive “silence” truth field, fixed carriers, assumptions,
and claim widening.

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
The same-key-cancellation milestone contributes 11 reviewed theorem types.

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

## Exact non-claim

The typed restoration operation and its complete coordinate maps remain
explicit inputs. The successor ambient-ledger milestone accepts an exact
proof-bearing binding of these cells into an explicit ambient BN4 ledger while
retaining a candidate-derived BN4 kernel, but does not derive that binding or
ledger from the candidate. This
result therefore does not construct semantic restorations from a terminal candidate, embed
cancellation or Hall outcomes into the complete global route system, prove
global route silence or the full historical PkgC theorem, derive the complete
BN6/Packet selector-realizer pipeline, prove polynomial generation or runtime,
ZeroSlack or PCCMin, put SAT in P, remove a project assumption, or prove
`P = NP`.

## Verification

From a checkout with the pinned Lean toolchain:

```bash
lake build PNP.ResidualTerminalPkgCSameKeyCancellation
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPkgCSameKeyCancellationAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPkgCSameKeyCancellation.lean
node --test audits/lean-residual-terminal-pkgc-same-key-cancellation0.test.mjs
```
