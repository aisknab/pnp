# Checked Packet semantic/HN activity binding milestone

## Objective

Bind the four exact non-budget Packet mismatches still exposed by the current
canonical selector-faithfulness payload to the existing finite HB
hereditary-normalization activity table. The binding is checked exhaustively
over every canonical selector handle. When the already formalized no-outcome
HB closure proves every activity bit false, the checked binding forces exact
frontier, obligation, activation, and direction agreement.

Compose that result with the separately checked budget/HB binding. Every
semantic first route is then excluded, so the positive-Packet endpoint retains
only the exact residual-nondecrease route already computed from the
ten-coordinate RankWF comparison.

## Legacy anchor and dependency edge

The pinned manuscript's Packet boundary orders frontier, obligation,
activation, direction, and budget checks before rank descent. Its simultaneous
HB layer separates hereditary-normalization and budget activity. The current
formal reconstruction already gives exact meanings to all four non-budget
semantic failures and separately maps a budget mismatch to the HB budget node.
It does not connect the remaining four failures to the HN activity row at the
selector's authoritative rank. This milestone closes precisely that supplied,
locally checkable Packet-to-HN edge.

## Unbounded abstraction

For an arbitrary finite grouped BN6 family, arbitrary finite rank carrier, and
arbitrary typed frontier, obligation, activation, and direction domains with
decidable equality, define exact semantic agreement as the conjunction of the
four source/selector equalities. Define a binding proposition requiring every
canonical handle that fails this conjunction to activate
`environment.hnActive` at `environment.rankOf handle`.

The Boolean checker enumerates the family's complete input-relative handle
list and accepts a row exactly when all four equalities hold or the
authoritative HN activity bit is true. No selector position, family size, rank
count, field value, or concrete Packet instance is fixed.

## Exact theorem interface

The primary executable specification is:

```lean
theorem TerminalPacketTypedRealizerTable.checkPacketSemanticHNActivityBinding_eq_true_iff
    (table : TerminalPacketTypedRealizerTable current family rankCount) :
    table.checkPacketSemanticHNActivityBinding = true ↔
      table.PacketSemanticHNActivityBound
```

The closure consequence is:

```lean
theorem TerminalPacketTypedRealizerTable.packetSemanticFieldsAgree_of_checkedHNActivityBinding
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (bindingAccepted : table.checkPacketSemanticHNActivityBinding = true)
    (closureAccepted :
      dependencyTable.checkNoOutcomeActiveClosure table.environment = true)
    (handle : family.PacketSelectorHandle) :
    table.PacketSemanticFieldsAgree handle
```

The named positive-Packet endpoint additionally consumes the existing checked
budget/HB binding. It returns a canonical handle whose first route is exactly
`.descent`, whose failure evidence is tied to that route, and whose
after-rank is not lexicographically below its before-rank.

## Regression and hostile evidence

- Accept complete semantic agreement without HN activity.
- Accept each individual mismatch only when the authoritative ranked HN node
  is active.
- Reject frontier, obligation, activation, and direction mismatches
  independently when that node is inactive.
- Prove exhaustive Boolean/proposition equivalence over arbitrary finite
  handle lists.
- Combine accepted binding with checked HB closure to recover all four typed
  equalities and exclude every corresponding first route.
- Compose with the separately checked budget/HB binding and preserve exact
  residual-nondecrease evidence.
- Audit every new declaration for assumptions and prohibit fixed carrier
  bounds, caller-controlled success flags, erased fields, hidden route
  clearing, project axioms, or claim widening.

## Conservative claim boundary

The grouped family, BN5 coordinates, activation atoms, typed directions and
budgets, finite rank map, residual ranks, realizer claims, HN/BUD activity
tables, dependency rows, and both Packet-to-HB bindings remain explicit data.
The new checker verifies a supplied Packet-to-HN binding; it does not
construct that binding from terminal data, prove HN blocker semantics or
semantic dependency completeness, or derive the HB table.

Reducing the forced first route to `.descent` yields exact residual
nondecrease, not a decreasing replacement or a contradiction. The result does
not construct the grouped family or rank map, establish complete Packet
adequacy, close unconditional HB negative closure, construct the no-lower
ledger, prove ZeroSlack or PCCMin, establish encoded-size or
polynomial-runtime bounds, put SAT in P, remove a project assumption, or prove
P = NP.

## Downstream blockers

This theorem isolates the remaining `Formal.ZeroSlack` Packet route boundary
to the already explicit residual-nondecrease case. A later milestone must
construct or check the missing descent/no-lower connection rather than assume
it. `Formal.ResidualBandMinimizer`,
`Formal.PolynomialRuntimeAndCertificateBounds`, `Formal.ConcreteSAT`, and
`Formal.RootTheoremAndAxiomAudit` remain downstream and unchanged.

## Release gates

Run source-shape checks and the focused remote Lean target first, then the
focused regression, axiom transcript, hostile Node audit, generated
inventory/publication checks, one complete capped remote verification, and one
exact-head clean reproduction. Publish through a focused draft PR, require all
normal checks, merge manually, and reproduce the exact merge before the
whole-surface non-Lean PNPLabs synchronization and production gates.
