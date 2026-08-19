# Checked Packet descent/no-lower binding milestone

## Objective

Connect the exact residual-nondecrease route forced by the current checked
Packet/HB endpoint to one executable row of the pinned manuscript's no-lower
ledger.  Over every canonical selector handle in an arbitrary finite grouped
BN6 family, a Boolean checker requires the fully computed Packet first route
not to be `.descent`.  The M166 endpoint constructs a handle whose route is
exactly `.descent`, so the checker must reject.  If that local no-lower row is
claimed accepted under the same premises, Lean derives a contradiction.

## Legacy anchor and dependency edge

The pinned manuscript's Section 16 `Rank-parametric ZeroSlack` record says that
every packet-route failure is positively excluded by the no-lower ledger before
the positive-residual contradiction proceeds.  The current reconstruction
already proves that positive Packet existence, executable selector silence,
checked well-founded HB closure, and the two checked Packet-to-HB bindings force
one canonical handle to expose the final `.descent` route with exact residual
nondecrease.  It does not yet connect that forced route to an executable
no-lower rejection.

This milestone closes precisely that local ZSC-001 edge:

```text
positive BN6 Packet
  + checked Packet semantic/HN and budget/HB bindings
  + executable selector silence and checked HB no-outcome closure
  -> one exact computed .descent failure
  -> rejection of the checked Packet descent/no-lower row
```

## Unbounded abstraction

For an arbitrary finite grouped BN6 family, arbitrary finite selector-rank
carrier, arbitrary typed Packet semantic domains with decidable equality, and
arbitrary per-handle before/after ten-coordinate residual ranks, define the
local no-lower proposition as absence of the exact computed `.descent` first
route at every canonical handle.  Its Boolean checker enumerates the complete
input-relative handle list and compares the actual computed route, not a
caller-supplied `noLower` flag or proof field.

No family size, selector position, rank count, coordinate value, route fixture,
or concrete Packet instance is fixed.

## Exact theorem interface

The primary executable specification is:

```lean
theorem TerminalBN6GroupedFamily.checkPacketDescentNoLower_eq_true_iff
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget))
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle ->
      TerminalResidualRank) :
    family.checkPacketDescentNoLower rankOf beforeRank afterRank = true <->
      family.PacketDescentNoLower rankOf beforeRank afterRank
```

The executable rejection theorem consumes exactly the M166 premises and proves:

```lean
theorem TerminalBN6PacketConclusion.checkPacketDescentNoLower_eq_false_of_selectorSilence
    ... :
    family.checkPacketDescentNoLower table.environment.rankOf
      beforeRank afterRank = false
```

A corollary states that the same premises together with checker acceptance imply
`False`.  The named report-facing endpoint is the checker-rejection theorem, not
an assumption that the no-lower row succeeds.

## Regression and hostile evidence

- Accept arbitrary families when every canonical computed first route differs
  from `.descent`.
- Reject a family with one exact computed `.descent` route.
- Prove exhaustive Boolean/proposition equivalence over the complete canonical
  handle list.
- Reuse the M166 witness to prove exact checker rejection and the accepted-row
  contradiction.
- Derive the axiom transcript from every public declaration in the module.
- Reject fixed carrier or rank bounds, caller-controlled no-lower flags, erased
  computed routes, reversed Boolean meaning, weakened enumeration, project
  axioms, `sorry`, or claim widening.

## Conservative claim boundary

This is one checked local row of the no-lower ledger.  The grouped family, BN5
coordinates, activation atoms, directions, budgets, rank map, before/after
residual ranks, realizer claims, HN/BUD activity environment, dependency rows,
and both Packet-to-HB bindings remain explicit data.  Checker rejection does not
construct an accepted no-lower ledger from terminal input.

The milestone does not cover HResolve, BudgetResolve, normalization, named
obstruction, exact-route, saturation-loss, replay, or other global no-lower
rows.  It does not construct positive residual slack, SaturatePositive,
BCELReady, the grouped family, semantic values, ranks, blocker tables, or
unconditional HB closure.  It does not prove the full ZSC-001 ledger, ZeroSlack,
PCCMin, encoded-size or polynomial-runtime bounds, SAT in P, remove a project
assumption, or prove P = NP.

## Downstream blockers

The remaining `Formal.ZeroSlack` work must construct the complete no-lower
ledger and the terminal data that makes its rows accepted, integrate all global
routes, close unconditional HB negative closure, and complete the
positive-residual contradiction.  `Formal.ResidualBandMinimizer`,
`Formal.PolynomialRuntimeAndCertificateBounds`, `Formal.ConcreteSAT`, and
`Formal.RootTheoremAndAxiomAudit` remain downstream and unchanged.

## Release gates

Run source-shape checks and the focused remote Lean target first, then the
focused regression, axiom transcript, hostile Node audit, generated
inventory/publication checks, one complete capped remote verification, and one
exact-head clean reproduction.  Publish through a focused draft PR, require all
normal checks, merge manually, and reproduce the exact merge before the
whole-surface non-Lean PNPLabs synchronization and production gates.
