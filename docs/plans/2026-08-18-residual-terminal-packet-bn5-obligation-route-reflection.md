# BN5-bound Packet frontier-and-obligation route reflection milestone

## Objective

Bind the current Packet selector-faithfulness boundary to the typed frontier
and obligation fields already retained by one complete BN5 shadow coordinate.
Replace both the free `frontierChecked` and `obligationChecked` inputs at the
active canonical-payload interface with executable equality of the selected
source coordinate and selector coordinate projections. Preserve the already
computed grouped-footprint colour, positive source charge, canonical source
route, table-owned finite rank, and exact ten-coordinate residual-descent
checks.

## Legacy anchor and dependency edge

The pinned manuscript's Section 11.5 BN5 construction preserves frontier and
obligation state on every full-to-shadow edge. Section 11.6 says BN6 retains
those row-key payloads, and Section 13's Pair packet seed routes the first
frontier or obligation mismatch before selector faithfulness can be accepted.
The current Lean frontier milestone compares arbitrary typed signatures but
does not bind them to BN5, while the obligation field remains a caller Boolean.
This milestone closes both local interface gaps by projecting the two fields
from the existing complete `TerminalBN5ShadowCoordinate` type.

## Unbounded abstraction

Define a payload over arbitrary BN4 activation atoms, semantic signatures,
transport types, frontier values, charge owners, obligation values,
origin/kernel values, and mode-projection values. It carries one typed source
BN5 coordinate and one typed selector BN5 coordinate. All theorems range over
arbitrary finite grouped BN6 families, arbitrary finite rank carriers, and
arbitrary coordinate-field types with only the decidable equalities needed by
the executable checks. No carrier size, selector position, coordinate value,
or concrete Packet instance is fixed.

## Exact theorem interface

The two primary field theorems expose the exact executable propositions:

```lean
theorem TerminalPacketSelectorBN5ObligationPayload.frontierCheck_eq_true_iff
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    payload.frontierCheck = true ↔
      payload.sourceCoordinate.frontier =
        payload.selectorCoordinate.frontier

theorem TerminalPacketSelectorBN5ObligationPayload.obligationCheck_eq_true_iff
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    payload.obligationCheck = true ↔
      payload.sourceCoordinate.obligation =
        payload.selectorCoordinate.obligation
```

The named milestone endpoint returns one exact first route for a positive
Packet under checked selector silence and HB closure. Canonical colour, charge,
rank, and internal exact-route failures are excluded. A frontier route carries
BN5 frontier inequality, an obligation route carries BN5 obligation inequality,
and a descent route carries exact residual-rank nondecrease.

## Regression and hostile evidence

- Accept coordinates with equal frontier and obligation projections and reject
  each independent mismatch.
- Prove both Boolean directions and exact `.frontier` and `.obligation`
  first-route semantics in manuscript priority order.
- Prove canonical colour, charge, rank, and internal exact-route failures
  remain excluded.
- Preserve the exact positive-Packet/HB endpoint without route-clear or
  faithfulness-binding premises.
- Audit every declaration in the new module for assumptions and prohibit
  shortcuts, fixed carrier bounds, project axioms, caller-controlled success
  bits, erased BN5 coordinates, or claim widening.
- Pin only the reviewed public theorem interface in the compiled inventory and
  publication map.

## Conservative claim boundary

The two complete BN5 coordinates, grouped family, finite rank map,
before/after residual ranks, realizer claims, HN/BUD activity, dependency rows,
and finite-to-exact rank map remain explicit inputs. Projection equality proves
only equality of the supplied BN5 frontier and obligation fields. It does not
construct either coordinate from terminal data, prove a full BN5 matching edge,
derive the BN6 grouped family, discharge external full-mode obligations, or
establish the manuscript's complete frontier-faithful comparison theorem.

Activation, direction, and budget remain explicit Boolean fields. Their routes
still require external semantics and global integration. The result does not
establish complete route silence, unconditional HB negative closure, the
no-lower ledger, full SaturatePositive or BCELReady, ZeroSlack or PCCMin,
polynomial generation or runtime, SAT in P, remove a project assumption, or
prove P = NP.

## Release gates

Run source-shape checks and the focused remote Lean target first, then the
focused regression, axiom transcript, hostile Node audit, generated
inventory/publication checks, one complete capped remote verification, and one
exact-head clean reproduction. Publish through a focused draft PR, require all
normal checks, merge manually, and reproduce the exact merge before the
whole-surface non-Lean PNPLabs synchronization and production gates.
