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
The same-key-cancellation milestone contributes 11 reviewed theorem types.

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

## Exact non-claim

The typed restoration operation and its complete coordinate maps remain
explicit inputs. The generated opposite-sign cells are not yet proved to be
the cells of a terminal candidate's ambient BN4 ledger. This result therefore
does not construct semantic restorations from a terminal candidate, embed
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
