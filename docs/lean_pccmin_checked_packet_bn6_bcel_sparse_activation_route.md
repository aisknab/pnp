# Sparse proper-cut activation route

M200 turns M199's structural rejection into the exact proper-cut obstruction
needed at the checked BCEL activation boundary. It defines one canonical list
of every singleton and order-preserving pair from an arbitrary finite carrier,
filters out the complete carrier, and proves that the resulting proper-cut
family is duplicate-free and has length at most
`n + n * n` for carrier length `n`.

For every sparse positive V53 hypergraph with at least two anchors,
`PNP.DirectWire.terminalV53_smallProperCutEquation_iff_constantProperCuts`
proves that equality of the crossing weight and declared cut value on those
singleton and pair cuts is equivalent to the complete equation on every
nonempty proper cut. This is an arbitrary-finite result: it does not fix the
carrier, cell family, cut, candidate, circuit, or number of anchors, and its
implementation does not construct a powerset.

The total proof-bearing classifier
`classifyTerminalV53SmallProperCuts` checks the canonical list and returns one
of three typed outcomes:

- the carrier has fewer than two anchors;
- every proper cut has the required constant weight; or
- the first exact singleton-or-pair proper cut whose weight differs from the
  declared value.

The mismatch retains its carrier-sublist proof, nonemptiness and properness,
length-at-most-two bound, and exact unequal weight. The executable regressions
cover coherent and mismatching systems with two, three, and four anchors. In
particular, a positive non-full cell on a four-anchor carrier produces the
concrete pair cut containing that cell's two anchors rather than an opaque
shape failure.

At the checked PCC boundary,
`PNP.DirectWire.pccmin_checked_packet_bn6_bcel_sparse_activation_route_or_zeroslack_checked_complete`
runs this classifier over M197's canonical positive-cell grouping. A coherent
result reuses M199's checked Packet/BN6/BCEL/HB conditional ZeroSlack branch.
A mismatch is reflected through M198's conservation theorem and returned as
one direct raw positive-cell activation weight that differs from the checked
BCEL defect.

## Claim boundary

The terminal problem, checked BCEL-ready certificate, raw positive cells and
payloads, realizer table, accepted claims, ranks, route-clear result,
dependency table, checked HB closure, resolvers, and normalizer remain supplied.
M200 does not derive the raw cells from BN3, BN4, BN5, PkgC, or every terminal
input.

An activation mismatch is an exact diagnostic obstruction, not yet a verified
gain or a globally rank-decreasing transition. The quadratic theorem covers
only the singleton/pair cut list. It is not an encoded-input polynomial bound
for terminal construction, raw cells, selectors, claims, tables, blockers,
certificates, or complete PCCMin runtime; upstream work may still enumerate
subsets.

M200 therefore does not close complete PkgC/BN3--BN6 integration, prove
manuscript-wide `SaturatePositive` or `BCELReady`, establish unconditional
`ZeroSlack`, construct polynomial `PCCMin`, put CNFSAT in P, close a global
gate, create `PNP.Main.p_eq_np`, or prove P = NP.

Formal artefact coverage is 176 of 178 current scoped rows. The separate
risk-weighted proof-completion estimate remains 35 percent, its uncertainty
range remains 20 to 40 percent, and zero of five global gates are closed.

## Verification

```text
lake build PNP
lake env lean -DwarningAsError=true lean-regression/PNPPCCMinCheckedPacketBN6BCELSparseActivationRoute.lean
lake env lean -DwarningAsError=true lean-audit/PNPPCCMinCheckedPacketBN6BCELSparseActivationRouteAxiomAudit.lean
node --test audits/lean-pccmin-checked-packet-bn6-bcel-sparse-activation-route0.test.mjs
```

The axiom transcript covers thirty reviewed declarations. The publication
gate rejects project-specific axioms, `sorryAx`, and `Classical.choice`.
