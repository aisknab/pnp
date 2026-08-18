# Typed Packet budget-route reflection milestone

## Objective

Bind the current Packet selector-faithfulness budget boundary to the typed
source and selector budget values carried by the manuscript's Packet atom
payload. Replace the last free `budgetChecked` input at the active canonical
payload interface with executable equality of those two values. Preserve the
already computed BN5 frontier and obligation checks, BN4 activation, typed
direction equality, grouped-footprint colour, positive source charge,
canonical source route, table-owned finite rank, and exact ten-coordinate
residual descent.

## Legacy anchor and dependency edge

The pinned manuscript's Section 13 Pair packet payload contains an explicit
`Bud(u)` coordinate. The Pair packet seed routes the first budget mismatch
after frontier, charge, obligation, activation, and direction checks and
before rank. The preceding typed-direction endpoint still accepts
`budgetChecked` as its sole caller Boolean. This milestone closes that local
interface gap by retaining typed source and selector budget values and
comparing them directly.

## Unbounded abstraction

Define a budget payload over arbitrary activation atoms, semantic signatures,
transport types, frontier values, charge owners, obligation values,
origin/kernel values, mode-projection values, direction values, and budget
values. It contains the existing typed direction payload plus one typed source
budget and one typed selector budget. All theorems range over arbitrary finite
grouped BN6 families, arbitrary finite rank carriers, and arbitrary field
types with only the decidable equalities needed by the executable checks. No
carrier size, selector position, budget value, or concrete Packet instance is
fixed.

## Exact theorem interface

The primary field theorem exposes the executable proposition exactly:

```lean
theorem TerminalPacketSelectorBN5BudgetPayload.budgetCheck_eq_true_iff
    (payload : TerminalPacketSelectorBN5BudgetPayload rankCount
      ActivationAtom SemanticSignature TransportType Frontier ChargeOwner
      Obligation OriginKernel ModeProjection Direction Budget) :
    payload.budgetCheck = true ↔
      payload.sourceBudget = payload.selectorBudget
```

The named milestone endpoint returns one exact first route for a positive
Packet under checked selector silence and HB closure. Canonical colour,
charge, rank, and internal exact-route failures are excluded. Frontier,
obligation, activation, and direction routes retain their exact ordered
semantics. A budget route carries all four prior equalities and exact typed
budget inequality, while a descent route carries exact residual-rank
nondecrease.

## Regression and hostile evidence

- Accept equal typed budgets and reject an independent budget mismatch, even
  when the inherited caller budget bit disagrees.
- Prove both Boolean directions and exact `.frontier`, `.obligation`,
  `.activation`, `.direction`, and `.budget` first-route semantics in
  manuscript order.
- Prove canonical colour, charge, rank, and internal exact-route failures
  remain excluded.
- Preserve the exact positive-Packet/HB endpoint without route-clear or
  faithfulness-binding premises.
- Audit every declaration in the new module for assumptions and prohibit
  shortcuts, fixed carrier bounds, project axioms, caller-controlled success
  bits, erased budget values, or claim widening.
- Pin only the reviewed public theorem interface in the compiled inventory and
  publication map.

## Conservative claim boundary

The typed budgets and directions, complete BN5 coordinates, grouped family,
finite rank map, before/after residual ranks, realizer claims, HN/BUD activity,
dependency rows, and finite-to-exact rank map remain explicit inputs. Budget
equality proves only equality of the supplied `Bud(u)` values. It does not
construct those values or coordinates from terminal data, prove the budget
envelope or external selector semantics, identify the local check with
BudgetResolve/HB activity, derive the BN6 grouped family, or establish the
manuscript's complete Packet adequacy bridge.

All local Packet classifier fields are now computed, but complete external
route adequacy and global route silence remain open. The result does not
establish unconditional HB negative closure, the no-lower ledger, full
SaturatePositive or BCELReady, ZeroSlack or PCCMin, polynomial generation or
runtime, SAT in P, remove a project assumption, or prove P = NP.

## Release gates

Run source-shape checks and the focused remote Lean target first, then the
focused regression, axiom transcript, hostile Node audit, generated
inventory/publication checks, one complete capped remote verification, and
one exact-head clean reproduction. Publish through a focused draft PR,
require all normal checks, merge manually, and reproduce the exact merge
before the whole-surface non-Lean PNPLabs synchronization and production
gates.
