# Exact Packet first-route failure semantics milestone

## Objective

Upgrade the total first-route classifier from a bare route witness to an exact
proof of the earliest failed payload condition. For all ten constructors of
`TerminalPacketSelectorFaithfulnessRoute`, one uniform theorem must identify
the preceding successful checks and the exact current failed check. The result
must lift through every canonical handle in an arbitrary finite grouped BN6
family and through the positive-Packet/HB endpoint.

## Legacy anchor and dependency edge

The legacy anchors are Section 14 `Selector realization`, especially its rule
that a preservation failure exposes the first named field route, and Section
16 `Rank-parametric ZeroSlack`, whose no-lower ledger must exclude every named
packet-route failure rather than record an uninterpreted tag.

The exact dependency edge is:

```text
positive BN6 Packet
  + canonical payload faithfulness table
  + executable selector silence and HB active-dependency closure
  -> one canonical first-route tag
  -> the exact earliest failed payload condition for that tag
```

The unbounded abstraction is an arbitrary payload rank, arbitrary finite
grouped BN6 family, arbitrary canonical handle, and all constructors of the
closed route type. No fixed rank, carrier, route constructor, or fixture earns
milestone credit.

## Exact theorem boundary

Define the route-indexed proposition:

```text
TerminalPacketSelectorFaithfulnessPayload.FailureAt expectedRank route
```

It states that every field preceding `route` accepted and that the exact field
named by `route` failed. The core equivalence is:

```text
payload.firstRoute expectedRank = some route
  <-> payload.FailureAt expectedRank route
```

The named endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_computed_faithfulness_hb_first_route_failure
```

For a positive `TerminalBN6PacketConclusion`, canonicalized typed-realizer
table, dependency table, accepted selector-silence check, and accepted HB
active-dependency closure, it returns a canonical handle and route together
with both the executable first-route equality and the exact `FailureAt` proof.
It takes no route-clear premise and no independent faithfulness-binding
premise.

## Checked interface

1. Define all ten earliest-failure propositions in the executable priority
   order.
2. Prove `firstRoute = some route` if and only if the corresponding exact
   earliest-failure proposition holds.
3. Prove checker rejection if and only if some exact earliest-failure
   proposition holds.
4. Lift the route equivalence to the canonical source payload behind every
   grouped-family handle.
5. Strengthen the existing positive-Packet/HB outcome with the exact failure
   proof and expose one named milestone endpoint.
6. Pin the complete theorem types in the compiled inventory, axiom transcript,
   publication map, regression, and hostile source audit.

## Regression and hostile evidence

- Exercise every route constructor, including the rank mismatch and both final
  route-clear/descent fields.
- Exercise the generic equivalence, rejection/exact-failure equivalence,
  canonical grouped-family lift, and HB-forced positive-Packet endpoint.
- Reject a reordered route priority, a weakened proposition that omits earlier
  accepted fields, an existential tag without `FailureAt`, replacement of the
  canonical source payload, reintroduced route-clear or binding premises,
  fixed finite bounds, assumptions, and theorem-name overclaims.
- Derive the axiom transcript from every public declaration and retain only the
  reviewed Lean-standard axiom boundary.

## Conservative claim boundary

This milestone proves the exact semantics of the existing data-only Boolean
classifier. It does not prove that any Boolean field has the manuscript's
external terminal-data meaning, construct those fields, or show that the
reported condition is a sound decreasing route in a complete global outcome
system. The grouped family, payload fields, rank assignment, realizer claims,
activity functions, dependency rows, and finite-to-exact rank map remain
explicit inputs.

It does not establish external selector compatibility, complete route silence,
unconditional HB negative closure, `PNP.Main.zero_slack_complete`, PCCMin
exactness, encoded-size or polynomial-runtime bounds, SAT in P, remove a project
assumption, or prove `P = NP`.

## Remaining downstream blockers

1. Construct or reflect every payload field from terminal data and prove the
   external adequacy of each route condition.
2. Map all externally adequate routes into one decreasing complete global
   outcome system and construct the no-lower ledger.
3. Construct the grouped family, rank assignment, exhaustive realizer claims,
   blocker activity, and dependency rows with external selector compatibility.
4. Close unconditional HB negative closure and ZeroSlack with encoded-size
   bounds.
5. Prove PCCMin exactness, polynomial runtime and certificate bounds, then the
   concrete root theorem and final axiom audit.

## Release gates

Run source-shape checks and the focused regression first. Build the exact Lean
dependency and root remotely before the axiom audit. After source and expected
interfaces stabilize, regenerate the theorem inventory, formal status,
publication map, and canonical report on the remote builder, run the complete
repository suite, and reproduce the exact PR head from a fresh checkout. Then
use the normal core PR, PNPLabs full-surface audit without Lean duplication,
manual merges, exact-merge reproduction, deployment, and production
verification sequence.
