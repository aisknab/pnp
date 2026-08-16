# Rank-reflected Packet descent route milestone

## Objective

Remove the caller-controlled Boolean at the final Packet selector descent
boundary.  The canonical payload used by the active Packet/HB endpoint must
replace `strictDescentClear` with the executable comparison on the already
formalized ten-coordinate `TerminalResidualRank`.  A reported final descent
failure must therefore carry a kernel proof that the supplied after-rank does
not strictly precede the supplied before-rank.

## Legacy anchor and dependency edge

The legacy anchors are Section 14 `Selector realization` and Section 16
`Rank-parametric ZeroSlack`, composed with the reconstructed `RankWF` order.
The exact dependency edge is:

```text
positive BN6 Packet
  + canonical payload computation
  + supplied before/after ten-coordinate ranks
  + executable selector silence and HB active-dependency closure
  -> one exact earliest Packet failure
  -> either an earlier field route
     or proof that the supplied transition is not RankWF-decreasing
```

The construction is uniform over an arbitrary finite grouped BN6 family,
arbitrary finite selector-rank carrier, and arbitrary per-handle residual
ranks.  No fixed carrier, rank prefix, route fixture, or coordinate bound earns
milestone credit.

## Exact theorem boundary

Define a canonical payload projection:

```text
payload.withComputedDescent before after
```

It preserves the first nine payload inputs exactly and replaces only
`strictDescentClear` with:

```text
terminalResidualRankLTBool after before
```

The final route equivalence must expose:

```text
(payload.withComputedDescent before after).firstRoute expectedRank =
    some .descent
  <->
all nine preceding conditions accepted /\ not (after.LexLT before)
```

The named endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_rank_reflected_hb_first_route_failure
```

It canonicalizes the HB faithfulness function with the rank-reflected payload,
preserves the supplied rank map, claims, and HN/BUD activity, and requires no
caller-supplied descent-binding or route-clear premise.  Every positive Packet
under accepted executable selector silence and HB active-dependency closure
returns an exact first route and failure proof, plus the disjunction that the
route is earlier than `.descent` or the supplied transition is not decreasing.

## Checked interface

1. Canonically replace only the final descent Boolean with the exact RankWF
   comparison and prove every preserved field equation.
2. Prove accepted computed payloads carry an actual `after.LexLT before`
   witness.
3. Prove `.descent` is returned exactly when every preceding field accepts and
   the supplied transition is not decreasing.
4. Lift the computation to every canonical source payload in an arbitrary
   finite grouped family.
5. Rebuild the typed-realizer faithfulness function from the rank-reflected
   payload while preserving rank, claims, and blocker activity.
6. Strengthen the positive-Packet/HB endpoint with exact failure evidence and
   the earlier-route-or-nondecrease conclusion.
7. Pin the complete public declaration surface in the compiled inventory,
   axiom transcript, publication map, regression, and hostile source audit.

## Regression and hostile evidence

- Show that a forged `strictDescentClear := true` is ignored when the supplied
  ranks are equal.
- Exercise both a genuinely decreasing last-coordinate transition and an
  equal-rank `.descent` failure.
- Exercise accepted-payload descent extraction, the grouped-family lift, table
  preservation, and the HB-forced endpoint.
- Reject restoration of the original caller Boolean, reversal of the
  before/after comparison, omission of a preceding condition, an independent
  binding premise, fixed finite bounds, assumptions, and theorem-name
  overclaims.
- Derive the axiom transcript from every public declaration and retain only the
  reviewed Lean-standard axiom boundary.

## Conservative claim boundary

This milestone reflects exactly one existing Packet field into one existing
formal semantic relation.  The before/after residual ranks and their assignment
to handles remain explicit inputs.  The first nine payload fields remain
explicit data, and their external manuscript meanings are not established.
An earlier route is retained as an exact Boolean-field failure, not yet mapped
into the complete global outcome system.

It does not construct the grouped family or ranks from a terminal candidate,
prove that any transition exists or decreases, map the other nine routes,
construct the no-lower ledger, establish complete route silence or
unconditional HB negative closure, prove unconditional ZeroSlack or PCCMin,
bound encoded size or polynomial runtime, put SAT in P, remove a project
assumption, or prove P = NP.

## Remaining downstream blockers

1. Reflect the remaining nine payload conditions from terminal data and map
   their failures into proof-bearing global outcomes.
2. Construct the grouped family, rank assignment, exhaustive realizer claims,
   blocker activity, and dependency rows with external selector compatibility.
3. Prove every admissible global route strictly decreases the complete rank and
   construct the no-lower ledger.
4. Close unconditional HB negative closure and ZeroSlack with encoded-size
   bounds.
5. Prove PCCMin exactness, polynomial runtime and certificate bounds, then the
   concrete root theorem and final axiom audit.

## Release gates

Run the focused source audit and exact new Lean targets first on the remote
builder.  After the theorem surface stabilizes, regenerate the compiled
inventory, formal status, publication map, and canonical report there, then run
the complete repository suite once and reproduce the exact PR head from a fresh
checkout.  Use the normal draft-PR, manual-merge, exact-merge reproduction,
PNPLabs whole-site audit without Lean duplication, deployment, and independent
production-verification sequence.
