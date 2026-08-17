# Canonical Packet rank-tag route reflection milestone

## Objective

Remove the caller-controlled finite-rank tag at the Packet selector
faithfulness boundary. The canonical payload already has an authoritative
handle rank supplied by the typed-realizer table, so the payload used by the
active Packet/HB endpoint must copy that rank mechanically while retaining the
previously computed ten-coordinate residual-rank descent check. A forged
payload rank therefore cannot manufacture a `.rank` failure.

## Legacy anchor and dependency edge

The legacy anchors are Section 14 `Selector realization` and Section 15 `HB`,
composed with the reconstructed finite selector-rank table and exact `RankWF`
order. The exact dependency edge is:

```text
positive BN6 Packet
  + canonical source payload
  + authoritative per-handle finite rank
  + supplied before/after ten-coordinate residual ranks
  + executable selector silence and HB active-dependency closure
  -> one exact earliest Packet failure
  -> never the duplicate rank-tag route
  -> either another unresolved field route
     or proof that the supplied transition is not RankWF-decreasing
```

The construction is uniform over an arbitrary finite grouped BN6 family,
arbitrary finite selector-rank carrier, and arbitrary per-handle residual
ranks. No fixed carrier, rank, route fixture, or coordinate bound earns
milestone credit.

## Exact theorem boundary

Define a canonical payload projection:

```text
payload.withComputedRankDescent expectedRank before after
```

It preserves the seven earlier Boolean fields and `exactRouteClear`, replaces
`rankTag` with `expectedRank`, and retains the executable comparison:

```text
terminalResidualRankLTBool after before
```

The rank-route theorem must expose:

```text
(payload.withComputedRankDescent expectedRank before after).firstRoute
    expectedRank != some .rank
```

The named endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_rank_tag_reflected_hb_first_route_failure
```

It rebuilds table faithfulness from the canonical source payload, the table's
own handle rank, and the supplied residual ranks. Under positive Packet,
accepted executable selector silence, and accepted HB active-dependency
closure, it returns an exact first route and failure proof, proves that route
is not `.rank`, and proves a final `.descent` route carries actual
nondecrease.

## Checked interface

1. Canonically replace `rankTag` with the authoritative expected handle rank
   while retaining the computed residual-rank descent bit and preserving every
   other payload field exactly.
2. Prove computed payload acceptance has no redundant rank-equality premise
   and still carries actual `after.LexLT before` evidence.
3. Prove `.rank` failure and `.rank` first-route outcomes are impossible for
   every payload and every finite rank.
4. Preserve exact final-route adequacy: `.descent` is returned exactly when
   the seven preceding Boolean fields and `exactRouteClear` accept and the
   supplied transition is nondecreasing.
5. Lift the computation and route exclusion to every canonical handle in an
   arbitrary finite grouped family.
6. Rebuild typed-realizer faithfulness from the rank-tag/reflected-descent
   payload while preserving the table's rank map, claims, and blocker activity.
7. Strengthen the positive-Packet/HB endpoint with exact failure evidence,
   rank-route exclusion, and the earlier-route-or-nondecrease conclusion.
8. Pin the complete public declaration surface in the compiled inventory,
   axiom transcript, publication map, regression, and hostile source audit.

## Regression and hostile evidence

- Show that a forged payload `rankTag` is ignored even when it differs from
  the table-owned expected rank.
- Exercise a genuinely decreasing transition, an equal-rank `.descent`
  failure, exact-route failure, grouped-family lifting, table preservation,
  and the HB-forced endpoint.
- Reject restoration of the caller rank tag, omission of the computed descent
  composition, a rank-route existential, an independent rank-binding premise,
  fixed finite bounds, assumptions, and theorem-name overclaims.
- Derive the axiom transcript from every public declaration and retain only
  the reviewed Lean-standard axiom boundary.

## Conservative claim boundary

This milestone removes one duplicate caller-controlled field by copying the
already supplied canonical handle rank. It does not construct the rank map or
residual ranks from a terminal candidate. The first seven Boolean payload
fields and `exactRouteClear` remain explicit data, and their external
manuscript meanings are not established. A non-rank route remains an exact
Boolean-field failure, not yet a proof-bearing complete global outcome.

It does not construct the grouped family, realizer claims, blocker activity,
or dependency rows; prove that a decreasing transition exists; map the eight
remaining routes into the global outcome system; construct the no-lower
ledger; establish complete route silence or unconditional HB negative
closure; prove unconditional ZeroSlack or PCCMin; bound encoded size or
polynomial runtime; put SAT in P; remove a project assumption; or prove
P = NP.

## Remaining downstream blockers

1. Reflect the seven earlier Boolean payload conditions and
   `exactRouteClear` from terminal data and map their failures into
   proof-bearing global outcomes.
2. Construct the grouped family, rank assignment, exhaustive realizer claims,
   blocker activity, and dependency rows with external selector compatibility.
3. Prove every admissible global route strictly decreases the complete rank
   and construct the no-lower ledger.
4. Close unconditional HB negative closure and ZeroSlack with encoded-size
   bounds.
5. Prove PCCMin exactness, polynomial runtime and certificate bounds, then the
   concrete root theorem and final axiom audit.

## Release gates

Run the focused source audit and exact new Lean targets first on the remote
builder. After the theorem surface stabilizes, regenerate the compiled
inventory, formal status, publication map, and canonical report there, then
run the complete repository suite once. Use the normal draft-PR, CI,
manual-merge, exact-merge
reproduction, PNPLabs whole-site publication audit without rebuilding Lean,
deployment, and independent production-verification sequence.
