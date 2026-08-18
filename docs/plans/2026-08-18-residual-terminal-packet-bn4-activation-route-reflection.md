# BN4 activation-exact Packet route reflection milestone

## Objective

Bind the current Packet selector-faithfulness activation boundary to the nested
BN4 activation keys already retained by the typed source and selector BN5
coordinates. Replace the free `activationChecked` input at the active
canonical-payload interface with executable equality of the two activation
atoms. Preserve computed BN5 frontier and obligation checks, grouped-footprint
colour, positive source charge, the canonical source route, table-owned finite
rank, and exact ten-coordinate residual descent.

## Legacy anchor and dependency edge

The pinned manuscript's Section 11.3 BN4 construction cancels only cells with
the same activation behavior and complete typed key. Section 11.4 retains that
key in every BN5 shadow coordinate, and Section 13 routes an activation
mismatch before later direction or budget checks. The current BN5-bound Packet
milestone still accepts `activationChecked` as a caller Boolean. This
milestone closes that local dependency edge by projecting the activation atom
from the existing complete coordinate and reusing
`terminalBN4ActivationCode_eq_iff_activation`.

## Unbounded abstraction

All theorems range over arbitrary finite grouped BN6 families, arbitrary finite
rank carriers, and arbitrary BN5 coordinate-field types. Only decidable
equality of the activation atom, frontier, obligation, and family anchor types
is required by the executable boundary. No carrier size, selector position,
coordinate value, cut universe, or concrete Packet instance is fixed.

## Exact theorem interface

The primary extensional theorem is:

```lean
theorem TerminalPacketSelectorBN5ObligationPayload.activationCheck_eq_true_iff_activation
    (payload : TerminalPacketSelectorBN5ObligationPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection) :
    payload.activationCheck = true ↔
      ∀ cut,
        (TerminalBN4CodeActive
            (terminalBN4ActivationCode payload.sourceCoordinate.key.atom) cut ↔
          TerminalBN4CodeActive
            (terminalBN4ActivationCode payload.selectorCoordinate.key.atom)
              cut)
```

The named milestone endpoint returns one exact first route for a positive
Packet under checked selector silence and HB closure. Canonical colour, charge,
rank, and internal exact-route failures are excluded. A frontier route carries
BN5 frontier inequality, an obligation route carries prior frontier equality
and BN5 obligation inequality, an activation route carries both earlier
equalities and BN4 activation-atom inequality, and a descent route carries
exact residual-rank nondecrease.

## Regression and hostile evidence

- Accept equal activation atoms and reject an independent activation mismatch,
  even when the inherited caller activation bit is false.
- Prove both Boolean directions and extensional activation-predicate equality
  on every cut without enumerating the cut universe.
- Prove exact `.frontier`, `.obligation`, and `.activation` first-route
  semantics in manuscript priority order.
- Prove canonical colour, charge, rank, and internal exact-route failures
  remain excluded.
- Preserve the exact positive-Packet/HB endpoint without route-clear or
  faithfulness-binding premises.
- Audit every declaration in the new module for assumptions and prohibit
  shortcuts, fixed carrier bounds, project axioms, caller-controlled success
  bits, erased activation semantics, or claim widening.
- Pin only the reviewed public theorem interface in the compiled inventory and
  publication map.

## Conservative claim boundary

The complete BN5 coordinates, grouped family, finite rank map, before/after
residual ranks, realizer claims, HN/BUD activity, dependency rows, and
finite-to-exact rank map remain explicit inputs. Activation equality proves
only equality of the canonical BN4 activation predicates represented by the
supplied coordinate atoms. It does not construct either coordinate from
terminal data, prove a full BN4 or BN5 matching edge, derive the BN6 grouped
family, discharge external full-mode obligations, or establish complete Packet
adequacy.

Direction and budget remain explicit Boolean fields. Their two routes still
require external semantics and global integration. The result does not
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
