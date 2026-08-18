# Typed Packet direction-route reflection milestone

## Objective

Bind the current Packet selector-faithfulness direction boundary to the typed
source and selector direction values carried by the manuscript's Packet atom
payload. Replace the free `directionChecked` input at the active canonical
payload interface with executable equality of those two values. Preserve the
already computed BN5 frontier and obligation checks, BN4 activation check,
grouped-footprint colour, positive source charge, canonical source route,
table-owned finite rank, and exact ten-coordinate residual descent.

## Legacy anchor and dependency edge

The pinned manuscript's Section 13 Pair packet payload contains an explicit
`Dir(u)` coordinate. The Pair packet seed routes the first direction mismatch
after frontier, charge, obligation, and activation checks and before the
budget check. Section 11.6 states that BN6 preserves direction in every
positive packet atom. The current BN4-activation-reflected Packet endpoint
still accepts `directionChecked` as a caller Boolean. This milestone closes
that local interface gap by retaining typed source and selector direction
values and comparing them directly.

## Unbounded abstraction

Define a direction payload over arbitrary BN4 activation atoms, semantic
signatures, transport types, frontier values, charge owners, obligation
values, origin/kernel values, mode-projection values, and direction values.
It contains the existing typed source and selector BN5 coordinates plus one
typed source direction and one typed selector direction. All theorems range
over arbitrary finite grouped BN6 families, arbitrary finite rank carriers,
and arbitrary field types with only the decidable equalities needed by the
executable checks. No carrier size, selector position, direction value, or
concrete Packet instance is fixed.

## Exact theorem interface

The primary field theorem exposes the executable proposition exactly:

```lean
theorem TerminalPacketSelectorBN5DirectionPayload.directionCheck_eq_true_iff
    (payload : TerminalPacketSelectorBN5DirectionPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection Direction) :
    payload.directionCheck = true ↔
      payload.sourceDirection = payload.selectorDirection
```

The named milestone endpoint returns one exact first route for a positive
Packet under checked selector silence and HB closure. Canonical colour,
charge, rank, and internal exact-route failures are excluded. A frontier route
carries exact BN5 frontier inequality, an obligation route carries prior
frontier equality and exact BN5 obligation inequality, an activation route
carries both earlier equalities and exact activation-atom inequality, a
direction route carries all earlier equalities and exact typed direction
inequality, and a descent route carries exact residual-rank nondecrease.

## Regression and hostile evidence

- Accept equal typed directions and reject an independent direction mismatch,
  even when the inherited caller direction bit disagrees.
- Prove both Boolean directions and exact `.frontier`, `.obligation`,
  `.activation`, and `.direction` first-route semantics in manuscript order.
- Prove canonical colour, charge, rank, and internal exact-route failures
  remain excluded.
- Preserve the exact positive-Packet/HB endpoint without route-clear or
  faithfulness-binding premises.
- Audit every declaration in the new module for assumptions and prohibit
  shortcuts, fixed carrier bounds, project axioms, caller-controlled success
  bits, erased direction values, or claim widening.
- Pin only the reviewed public theorem interface in the compiled inventory and
  publication map.

## Conservative claim boundary

The typed directions, complete BN5 coordinates, grouped family, finite rank
map, before/after residual ranks, realizer claims, HN/BUD activity, dependency
rows, and finite-to-exact rank map remain explicit inputs. Direction equality
proves only equality of the supplied `Dir(u)` values. It does not construct
those values or coordinates from terminal data, prove their transport or
external selector semantics, derive the BN6 grouped family, or establish the
manuscript's complete Packet adequacy bridge.

Budget is the sole remaining supplied Boolean field. Its route still requires
external semantics and global integration. The result does not establish
complete route silence, unconditional HB negative closure, the no-lower
ledger, full SaturatePositive or BCELReady, ZeroSlack or PCCMin, polynomial
generation or runtime, SAT in P, remove a project assumption, or prove P = NP.

## Release gates

Run source-shape checks and the focused remote Lean target first, then the
focused regression, axiom transcript, hostile Node audit, generated
inventory/publication checks, one complete capped remote verification, and one
exact-head clean reproduction. Publish through a focused draft PR, require all
normal checks, merge manually, and reproduce the exact merge before the
whole-surface non-Lean PNPLabs synchronization and production gates.
