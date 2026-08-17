# Canonical Packet exact-route reflection milestone

## Objective

Remove the caller-controlled `exactRouteClear` bit at the Packet selector
faithfulness boundary. Every canonical handle already materializes one exact
input-relative grouped cell and one original positive payload atom, with proofs
of group membership, footprint equality, and atom membership. The canonical
payload used by the active Packet/HB endpoint must therefore mark this internal
handle-to-source route clear by construction while retaining the authoritative
finite rank and executable ten-coordinate residual-rank descent checks.

## Legacy anchor and dependency edge

The legacy anchors are Section 14 `Selector realization` and Section 15 `HB`,
composed with the reconstructed total selector decoder, payload realization,
finite selector-rank table, and exact `RankWF` order. The exact dependency edge
is:

```text
positive BN6 Packet
  + canonical input-relative handle
  + exact source cell and original positive payload atom
  + authoritative per-handle finite rank
  + supplied before/after ten-coordinate residual ranks
  + executable selector silence and HB active-dependency closure
  -> one exact earliest Packet failure
  -> never the duplicate exact-route or rank-tag routes
  -> either one of seven unresolved semantic-field routes
     or proof that the supplied transition is not RankWF-decreasing
```

The construction is uniform over an arbitrary finite grouped BN6 family,
arbitrary finite selector-rank carrier, and arbitrary per-handle residual
ranks. No fixed carrier, route fixture, or coordinate bound earns milestone
credit.

## Exact theorem boundary

Define a canonical payload projection:

```text
payload.withComputedExactRouteRankDescent expectedRank before after
```

It preserves the seven unresolved Boolean fields, sets `exactRouteClear` from
the already proved canonical handle-to-cell-to-atom realization, copies the
authoritative expected rank, and computes the final descent bit from:

```text
terminalResidualRankLTBool after before
```

The route theorems must expose:

```text
(payload.withComputedExactRouteRankDescent expectedRank before after).firstRoute
    expectedRank != some .exactRoute

(payload.withComputedExactRouteRankDescent expectedRank before after).firstRoute
    expectedRank != some .rank
```

The named endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_exact_route_reflected_hb_first_route_failure
```

It rebuilds table faithfulness from the canonical source realization, the
table-owned handle rank, and supplied residual ranks. Under positive Packet,
accepted executable selector silence, and accepted HB active-dependency
closure, it returns an exact first route and failure proof, excludes both
duplicate routes, and proves that a final `.descent` route carries actual
nondecrease.

## Checked interface

1. Canonically set `exactRouteClear` only at the total source-realization
   boundary, while copying the authoritative rank and computing residual
   descent.
2. Expose the source cell membership, exact footprint, original atom
   membership, and positive mass that justify the internal route reflection.
3. Prove canonical acceptance has no independent exact-route or rank-equality
   premise and still carries actual `after.LexLT before` evidence.
4. Prove `.exactRoute` and `.rank` failure and first-route outcomes are
   impossible for every canonicalized payload.
5. Preserve exact final-route adequacy: `.descent` is returned exactly when the
   seven preceding semantic Boolean fields accept and the supplied transition
   is nondecreasing.
6. Lift the computation and route exclusions to every canonical handle in an
   arbitrary finite grouped family.
7. Rebuild typed-realizer faithfulness while preserving the table's rank map,
   claims, and blocker activity.
8. Strengthen the positive-Packet/HB endpoint with exact failure evidence,
   both route exclusions, and the earlier-route-or-nondecrease conclusion.
9. Pin the complete public declaration surface in the compiled inventory,
   axiom transcript, publication map, regression, and hostile source audit.

## Regression and hostile evidence

- Show that a forged `exactRouteClear = false` value is ignored only after the
  payload is selected through the canonical handle realization.
- Exercise a genuine decreasing transition, an equal-rank `.descent` failure,
  all seven retained earlier routes, grouped-family lifting, table
  preservation, and the HB-forced endpoint.
- Reject direct use of a caller exact-route bit, omission of canonical source
  realization, restoration of the caller rank tag, omission of computed
  descent, either forbidden route existential, fixed finite bounds,
  assumptions, and theorem-name overclaims.
- Derive the axiom transcript from every public declaration and retain only
  the reviewed Lean-standard axiom boundary.

## Conservative claim boundary

This milestone reflects only the repository's already proved internal route:
one decoded input-relative handle selects one original positive payload atom
from its exact grouped cell and footprint. Setting the internal route bit does
not establish any broader manuscript claim about exact minima, optimal
replacement circuits, semantic selector compatibility, or completeness of a
global route system.

The seven earlier Boolean fields remain supplied and their external manuscript
meanings are not established. A remaining route is an exact Boolean-field
failure, not yet a proof-bearing complete global outcome. The grouped family,
rank map, before/after residual ranks, realizer claims, blocker activity, and
dependency rows remain explicit inputs.

It does not construct the grouped family or exhaustive realizer data; derive
the seven semantic fields from a terminal candidate; prove that a decreasing
transition exists; construct the no-lower ledger; establish complete route
silence or unconditional HB negative closure; prove unconditional ZeroSlack or
PCCMin; bound encoded size or polynomial runtime; put SAT in P; remove a
project assumption; or prove P = NP.

## Remaining downstream blockers

1. Reflect the seven semantic payload conditions from terminal data and map
   their failures into proof-bearing global outcomes.
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
run the complete core repository suite once. Use the normal draft-PR, CI,
manual-merge, exact-merge reproduction, PNPLabs whole-site publication audit
without rebuilding Lean, deployment, and independent production-verification
sequence.
