# Lean rank-reflected Packet descent route

This milestone connects the final Packet first-failure field to the existing
formal `RankWF` relation. Previously, `strictDescentClear` was one of the ten
supplied payload values. Exact first-route semantics could prove that this
Boolean was false, but could not conclude anything about a residual-rank
transition.

`ResidualTerminalPacketDescentRouteReflection` removes that choice at the
active endpoint. `withComputedDescent before after` preserves the first nine
payload inputs and replaces the final field with
`terminalResidualRankLTBool after before`. Lean proves that acceptance carries
the actual proposition `after.LexLT before`, while a final `.descent` failure
carries its negation.

The computation lifts to the canonical positive source payload behind every
handle in an arbitrary finite grouped BN6 family. A rebuilt typed-realizer
table computes faithfulness from this rank-reflected payload while retaining
the supplied rank assignment, claims, and HN/BUD activity exactly. Under
accepted executable selector silence and HB active-dependency closure, every
positive Packet therefore exposes either an earlier exact field route or a
proof that its supplied transition is nondecreasing.

## Manuscript anchor and theorem boundary

The pinned manuscript anchors are Section 14 selector realization, Section 16
rank-parametric ZeroSlack, and the reconstructed ten-coordinate `RankWF`
order. This milestone joins one route to that order; it does not claim the
complete global route system.

The named endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_rank_reflected_hb_first_route_failure
```

It requires no route-clear premise and no separate descent-binding premise.
Its result contains a canonical handle, exact first route and `FailureAt`
proof, plus the disjunction that the route is earlier than `.descent` or the
supplied after-rank does not strictly precede the before-rank.

## Kernel-checked surface

The source is
[`lean/PNP/ResidualTerminalPacketDescentRouteReflection.lean`](../lean/PNP/ResidualTerminalPacketDescentRouteReflection.lean).
It provides:

- the computed-descent payload projection and exact field-preservation proof;
- validity, failure, and first-route equivalences against `RankWF`;
- extraction of actual descent from an accepted computed payload;
- canonical grouped-family faithful, first-route, and failure computations;
- a typed-realizer table whose faithfulness function uses those computations;
  and
- the total positive-Packet/HB earlier-route-or-nondecrease endpoint.

The regression and axiom audit are:

```text
lean-regression/PNPResidualTerminalPacketDescentRouteReflection.lean
lean-audit/PNPResidualTerminalPacketDescentRouteReflectionAxiomAudit.lean
audits/lean-residual-terminal-packet-descent-route-reflection0.test.mjs
```

The regression proves that an original forged `strictDescentClear := true` is
ignored for equal ranks, exercises an actual last-coordinate decrease, and
checks the generic, grouped-family, table, and HB contracts. The hostile audit
rejects restoring the caller Boolean, reversing the comparison, dropping an
earlier condition, changing the endpoint disjunction, adding a binding
premise, fixed finite bounds, assumptions, and theorem-name overclaims.

## Claim boundary

This is exact reflection for one field. The first nine payload fields,
before/after ranks, per-handle rank assignment, grouped family, realizer
claims, blocker activity, dependency rows, and finite-to-exact rank map remain
explicit. The module does not construct those ranks or data from a terminal
candidate, establish external manuscript semantics for the other nine fields,
map their routes into the complete global outcome system, prove that a
decreasing transition exists, or construct the no-lower ledger.

Accordingly, it does not establish complete route silence, unconditional HB
negative closure, positive slack, `SaturatePositive`, `BCELReady`,
unconditional ZeroSlack, PCCMin, encoded-size or polynomial-runtime bounds,
SAT in P, or `P = NP`.
