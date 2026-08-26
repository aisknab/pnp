# Canonical BCEL positive-cell grouping for BN6

M197 removes the already-grouped BN6 cell ledger from the M196 boundary. A
`TerminalBN6PositiveCell` now contains only one raw support list and one
strictly positive payload-bearing atom. Its footprint is computed by filtering
the checked BCEL carrier, which fixes carrier order, removes duplicate support
entries, and makes the result an exact duplicate-free carrier sublist.

For every canonical footprint, Lean constructs a V54 consumer system whose
minimal consumers are exactly the footprint singletons. It proves that the
system recovers the same singleton footprint and satisfies the PkgC
singletonization interface. A constructive finite traversal computes the
duplicate-free footprint universe, gathers every input payload atom at its
exact footprint, and emits one group per footprint. The grouping proofs needed
by M196 - common carrier, footprint size, and duplicate-free group footprints -
are all derived by the constructor. Every raw payload atom is proved to survive
in its unique canonical group.

`PCCMinCheckedPacketBN6BCELPositiveCells.groupedCells` installs this computed
ledger in M196. The public theorem is
`PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_grouping_route_or_zeroslack_checked_complete`.
Under the same complete checked selector-silence premise, it returns either
zero residual slack or one explicit nonempty proper cut whose constructed
family activation weight differs from the checked BCEL defect.

## Claim boundary

The raw support lists, positive masses, payload values, terminal problem,
checked BCEL-ready certificate, realizer table, claims, ranks, route-clear
equation, dependency table, and checked HB closure remain supplied. In
particular, M197 does not derive the raw cells, supports, or payloads from BN3,
BN4, BN5, PkgC, or every terminal input.

The remaining activation mismatch is diagnostic route evidence, not a verified
gain or globally decreasing transition. Canonical grouping does not enumerate
cuts, but the inherited M195 proper-cut classifier may enumerate a powerset.
No encoded-input-size polynomial theorem is claimed for the complete
construction.

M197 therefore does not close complete PkgC/BN3--BN6 integration, prove
manuscript-wide `SaturatePositive` or `BCELReady`, establish unconditional
`ZeroSlack`, construct polynomial `PCCMin`, put CNFSAT in P, close a global
gate, create `PNP.Main.p_eq_np`, or prove P = NP.

Formal artefact coverage is 173 of 175 current scoped rows. The separate
risk-weighted proof-completion estimate remains 35 percent, its uncertainty
range remains 20 to 40 percent, and zero of five global gates are closed.

## Verification

```text
lake build PNP
lake env lean -DwarningAsError=true lean-regression/PNPPCCMinCheckedPacketBN6BCELCanonicalGrouping.lean
lake env lean -DwarningAsError=true lean-audit/PNPPCCMinCheckedPacketBN6BCELCanonicalGroupingAxiomAudit.lean
node --test audits/lean-pccmin-checked-packet-bn6-bcel-canonical-grouping0.test.mjs
```

The axiom transcript covers 34 reviewed declarations. Their compiled closure
contains only `propext` and `Quot.sound`; it contains no project-specific axiom,
`sorryAx`, or `Classical.choice`.
