# Checked Packet budget/HB activity binding milestone

## Objective

Bind the typed Packet budget mismatch exposed by the current canonical
selector-faithfulness payload to the existing finite HB budget-activity table.
The binding is checked exhaustively over every canonical selector handle.  When
the already formalized no-outcome HB closure proves every activity bit false,
the checked binding forces exact source/selector budget equality and excludes
the `.budget` first route.

## Legacy anchor and dependency edge

The pinned manuscript's Section 13 Pair packet seed routes a `Bud(u)` mismatch,
Section 8.3's `BUD.BudgetResolver` supplies the budget/no-budget boundary, and
Section 15's simultaneous HN/BUD closure excludes active budget blockers by a
strict rank argument.  The typed-budget endpoint currently exposes a budget
mismatch but does not connect that mismatch to the HB `budgetActive` row at the
selector's authoritative rank.  This milestone closes that exact local
Packet-to-HB dependency edge.

## Unbounded abstraction

For an arbitrary finite grouped BN6 family, arbitrary finite rank carrier, and
arbitrary typed budget domain with decidable equality, define a binding
proposition requiring every canonical handle's budget inequality to imply
activity of the budget node at `environment.rankOf handle`.  Its Boolean
checker enumerates the family's complete input-relative handle list and tests
exactly the disjunction between typed equality and that activity bit.  No
selector position, family size, rank count, budget value, or concrete Packet
instance is fixed.

## Exact theorem interface

The primary executable specification is:

```lean
theorem TerminalPacketTypedRealizerTable.checkPacketBudgetHBActivityBinding_eq_true_iff
    (table : TerminalPacketTypedRealizerTable current family rankCount) :
    table.checkPacketBudgetHBActivityBinding = true ↔
      table.PacketBudgetHBActivityBound
```

The closure consequence is:

```lean
theorem TerminalPacketTypedRealizerTable.packetBudget_eq_of_checkedHBActivityBinding
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (bindingAccepted : table.checkPacketBudgetHBActivityBinding = true)
    (closureAccepted :
      dependencyTable.checkNoOutcomeActiveClosure table.environment = true)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadAtom handle).payload.sourceBudget =
      (family.packetSelectorPayloadAtom handle).payload.selectorBudget
```

The named positive-Packet endpoint composes this result with the existing
typed-budget first-route theorem.  Its forced route cannot be `.colour`,
`.charge`, `.rank`, `.exactRoute`, or now `.budget`; frontier, obligation,
activation, and direction retain their exact ordered mismatch meanings, while
`.descent` retains exact ten-coordinate nondecrease.

## Regression and hostile evidence

- Accept equality without activity and accept inequality only when the
  authoritative ranked budget node is active.
- Reject one inactive mismatch even when every other canonical handle is
  bound.
- Prove exhaustive Boolean/proposition equivalence over arbitrary finite
  handle lists.
- Combine accepted binding with checked HB closure to prove typed equality and
  exclude `.budget` from the canonical first-route classifier.
- Preserve the exact positive-Packet endpoint and all earlier route meanings.
- Audit every new declaration for assumptions and prohibit fixed carrier
  bounds, caller-controlled success flags, erased budget values, hidden route
  clearing, project axioms, or claim widening.

## Conservative claim boundary

The grouped family, typed source and selector budgets, BN5 coordinates,
directions, finite rank map, residual ranks, realizer claims, activity table,
and dependency rows remain explicit data.  The new checker verifies a supplied
Packet-to-HB binding; it does not construct that binding from terminal data,
implement the manuscript's full `Bud(u)` envelope or `BudgetResolve`, prove
budget-blocker semantic completeness, or derive the activity table.

Excluding the local budget route leaves frontier, obligation, activation,
direction, and descent outcomes.  It does not construct the grouped family or
rank map, prove complete Packet adequacy, map every remaining route into a
global decreasing outcome system, establish unconditional HB negative closure
or the no-lower ledger, prove ZeroSlack or PCCMin, establish encoded-size or
polynomial-runtime bounds, put SAT in P, remove a project assumption, or prove
P = NP.

## Downstream blockers

This theorem feeds the remaining `Formal.ZeroSlack` Packet-adequacy and global
route-silence work.  `Formal.ResidualBandMinimizer`,
`Formal.PolynomialRuntimeAndCertificateBounds`, `Formal.ConcreteSAT`, and
`Formal.RootTheoremAndAxiomAudit` remain downstream and unchanged.

## Release gates

Run source-shape checks and the focused remote Lean target first, then the
focused regression, axiom transcript, hostile Node audit, generated
inventory/publication checks, one complete capped remote verification, and one
exact-head clean reproduction.  Publish through a focused draft PR, require all
normal checks, merge manually, and reproduce the exact merge before the
whole-surface non-Lean PNPLabs synchronization and production gates.
