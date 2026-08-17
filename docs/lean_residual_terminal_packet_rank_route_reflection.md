# Lean canonical Packet rank-tag route reflection

This milestone removes a second duplicate input from the Packet
selector-faithfulness boundary. The typed-realizer table already assigns every
canonical handle one finite rank, but the source payload previously carried a
separate caller-supplied `rankTag`. Exact first-route semantics could identify
a mismatch as `.rank`; it could not prevent the two copies from disagreeing.

`ResidualTerminalPacketRankRouteReflection` replaces that payload field with
the authoritative expected handle rank. Its
`withComputedRankDescent expectedRank before after` projection also composes
the previous exact descent reflection, so it copies `expectedRank` into
`rankTag` and computes `strictDescentClear` as
`terminalResidualRankLTBool after before`. The seven earlier Boolean fields and
`exactRouteClear` are preserved exactly.

Lean proves that the resulting first-route classifier cannot return `.rank`.
Acceptance still carries the actual proposition `after.LexLT before`, while a
final `.descent` failure carries its negation. The computation lifts to every
canonical handle in an arbitrary finite grouped BN6 family and rebuilds table
faithfulness while preserving the table's rank map, claims, and HN/BUD
activity.

## Manuscript anchor and theorem boundary

The pinned manuscript anchors are Section 14 selector realization, Section 15
HB, and the reconstructed ten-coordinate `RankWF` order. This milestone
canonicalizes the duplicate finite rank at that boundary; it does not
construct the rank assignment from terminal data.

The named endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_rank_tag_reflected_hb_first_route_failure
```

Under a positive Packet, accepted executable selector silence, and accepted HB
active-dependency closure, it returns a canonical handle, exact first route,
and exact `FailureAt` proof. The route is proved not to be `.rank`; if it is
`.descent`, the supplied after-rank is proved not to strictly precede the
before-rank. No route-clear, rank-binding, or descent-binding premise is used.

## Kernel-checked surface

The source is
[`lean/PNP/ResidualTerminalPacketRankRouteReflection.lean`](../lean/PNP/ResidualTerminalPacketRankRouteReflection.lean).
It provides:

- a canonical rank-tag/descent payload projection and exact preservation
  theorem;
- validity and final-route equivalences against the authoritative finite rank
  and exact residual-rank relation;
- payload-level and grouped-family proofs that `.rank` cannot be returned;
- extraction of actual descent from an accepted computed payload;
- canonical grouped-family faithful, first-route, and failure computations;
- a typed-realizer table whose faithfulness function uses those computations;
  and
- the total positive-Packet/HB endpoint with exact failure, rank-route
  exclusion, and nondecrease evidence.

The focused checks are:

```bash
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketRankRouteReflection.lean
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketRankRouteReflectionAxiomAudit.lean
node --test audits/lean-residual-terminal-packet-rank-route-reflection0.test.mjs
```

The compiled axiom transcript is derived from every public declaration in
source order. The reviewed theorem surface reaches only `propext` and, for the
positive-Packet endpoints, `Quot.sound`; it does not use a project-specific
axiom, `Classical.choice`, `sorry`, native evaluation, or a fixed rank bound.

## Conservative boundary

The finite rank map and before/after residual ranks remain explicit inputs.
The seven earlier Boolean fields and `exactRouteClear` remain supplied and
their external manuscript semantics are not established. The eight remaining
routes are not yet mapped into a proof-bearing complete global outcome system.

This milestone does not construct the grouped family, rank map, realizer
claims, blocker activity, or dependency rows from a terminal candidate. It
does not prove existence of a decreasing transition, construct the no-lower
ledger, establish complete route silence or unconditional HB negative
closure, prove unconditional ZeroSlack or polynomial PCCMin, bound the
selector universe in encoded input size, prove polynomial runtime, put SAT in
P, remove a project assumption, or prove P = NP.
