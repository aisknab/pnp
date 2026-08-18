/-
Copyright (c) 2026 PNP Labs.

Checked binding from typed Packet budget mismatch to the existing HB budget
activity table.  The checker enumerates every canonical selector handle in an
arbitrary finite grouped BN6 family.  At each handle it requires either exact
source/selector budget equality or activity of the budget node at the table's
authoritative handle rank.

The already proved no-outcome HB closure forces every supplied HN/BUD activity
bit false.  Composing that closure with the checked binding therefore proves
typed budget equality at every handle and excludes `.budget` from the forced
Packet first-route outcome.

The typed budgets, grouped family, rank map, activity table, dependency rows,
residual ranks, realizer claims, and the checked binding itself remain explicit
inputs.  This module does not construct manuscript `Bud(u)` values or their
envelope from terminal data, implement BudgetResolve, prove blocker semantic
completeness, derive the HB tables, exclude the remaining semantic or descent
routes, establish unconditional HB negative closure, ZeroSlack, PCCMin,
polynomial runtime, SAT in P, remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketBudgetRouteReflection

namespace PNP
namespace DirectWire

variable {Anchor ActivationAtom SemanticSignature TransportType Frontier
  ChargeOwner Obligation OriginKernel ModeProjection Direction Budget : Type}
variable [DecidableEq Anchor] [DecidableEq Budget]

/-! ## Exhaustive Packet-to-HB budget binding -/

/-- Exact proposition checked at the local Packet/HB boundary: a typed budget
    mismatch at any canonical handle activates the budget node at that handle's
    authoritative finite rank. -/
def TerminalPacketTypedRealizerTable.PacketBudgetHBActivityBound
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount) : Prop :=
  ∀ handle : family.PacketSelectorHandle,
    (family.packetSelectorPayloadAtom handle).payload.sourceBudget ≠
        (family.packetSelectorPayloadAtom handle).payload.selectorBudget →
      table.environment.budgetActive
        (table.environment.rankOf handle) = true

/-- Exhaustively check exact budget equality or authoritative-rank budget
    activity for every canonical handle. -/
def TerminalPacketTypedRealizerTable.checkPacketBudgetHBActivityBinding
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount) : Bool :=
  family.packetSelectorHandles.all fun handle =>
    decide
        ((family.packetSelectorPayloadAtom handle).payload.sourceBudget =
          (family.packetSelectorPayloadAtom handle).payload.selectorBudget) ||
      table.environment.budgetActive (table.environment.rankOf handle)

/-- The Boolean scan recognizes exactly the all-handle Packet-to-HB budget
    activity proposition. -/
theorem TerminalPacketTypedRealizerTable.checkPacketBudgetHBActivityBinding_eq_true_iff
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount) :
    table.checkPacketBudgetHBActivityBinding = true ↔
      table.PacketBudgetHBActivityBound := by
  constructor
  · intro accepted handle mismatch
    have rowChecked := (List.all_eq_true.mp accepted) handle
      (family.mem_packetSelectorHandles handle)
    have alternatives :
        (family.packetSelectorPayloadAtom handle).payload.sourceBudget =
            (family.packetSelectorPayloadAtom handle).payload.selectorBudget ∨
          table.environment.budgetActive
            (table.environment.rankOf handle) = true := by
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using rowChecked
    exact alternatives.resolve_left mismatch
  · intro bound
    apply List.all_eq_true.mpr
    intro handle _handleMember
    by_cases equal :
        (family.packetSelectorPayloadAtom handle).payload.sourceBudget =
          (family.packetSelectorPayloadAtom handle).payload.selectorBudget
    · simp [equal]
    · simp [equal, bound handle equal]

/-! ## HB closure consequence -/

/-- Checked binding plus checked well-founded HB no-outcome closure forces exact
    typed budget equality at every canonical handle. -/
theorem TerminalPacketTypedRealizerTable.packetBudget_eq_of_checkedHBActivityBinding
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (bindingAccepted : table.checkPacketBudgetHBActivityBinding = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      table.environment = true)
    (handle : family.PacketSelectorHandle) :
    (family.packetSelectorPayloadAtom handle).payload.sourceBudget =
      (family.packetSelectorPayloadAtom handle).payload.selectorBudget := by
  by_cases equal :
      (family.packetSelectorPayloadAtom handle).payload.sourceBudget =
        (family.packetSelectorPayloadAtom handle).payload.selectorBudget
  · exact equal
  have bound :=
    (table.checkPacketBudgetHBActivityBinding_eq_true_iff).1 bindingAccepted
  have active := bound handle equal
  have inactive := dependencyTable.budgetActive_eq_false table.environment
    closureAccepted (table.environment.rankOf handle)
  rw [inactive] at active
  cases active

variable [DecidableEq ActivationAtom] [DecidableEq Frontier]
  [DecidableEq Obligation] [DecidableEq Direction]

/-- Consequently the canonical first-route classifier cannot report a budget
    mismatch after the checked Packet/HB binding and closure have passed. -/
theorem TerminalPacketTypedRealizerTable.packetSelectorBudgetFirstRoute_ne_of_checkedHBActivityBinding
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (bindingAccepted : table.checkPacketBudgetHBActivityBinding = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      table.environment = true)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        table.environment.rankOf beforeRank afterRank handle ≠
      some .budget := by
  intro found
  have semantics :=
    (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_budget_iff
      table.environment.rankOf beforeRank afterRank handle).1 found
  have equal := table.packetBudget_eq_of_checkedHBActivityBinding
    dependencyTable bindingAccepted closureAccepted handle
  exact semantics.2.2.2.2 equal

/-! ## Positive-Packet endpoint with the budget route removed -/

/-- Executable selector silence, HB closure, and the exhaustive budget binding
    force one exact earlier semantic route or exact residual nondecrease.  The
    local budget route is now impossible. -/
theorem TerminalBN6PacketConclusion.existsBudgetHBBoundFirstRouteFailure_of_selectorSilence
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (bindingAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).checkPacketBudgetHBActivityBinding = true)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          route ≠ .budget ∧
          (route = .frontier ∨ route = .obligation ∨ route = .activation ∨
            route = .direction ∨ route = .descent) ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) := by
  obtain ⟨handle, route, found, failure, notColour, notCharge, notRank,
      notExactRoute, _frontierMeaning, _obligationMeaning,
      _activationMeaning, _directionMeaning, _budgetMeaning,
      descentMeaning⟩ :=
    conclusion.existsBudgetReflectedFirstRouteFailure_of_selectorSilence table
      dependencyTable beforeRank afterRank silenceAccepted closureAccepted
  change table.checkPacketBudgetHBActivityBinding = true at bindingAccepted
  change dependencyTable.checkNoOutcomeActiveClosure table.environment = true at closureAccepted
  have notBudgetFound :
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
          table.environment.rankOf beforeRank afterRank handle ≠
        some .budget :=
    table.packetSelectorBudgetFirstRoute_ne_of_checkedHBActivityBinding
      dependencyTable beforeRank afterRank bindingAccepted closureAccepted handle
  have notBudget : route ≠ .budget := by
    intro routeEquation
    subst route
    exact notBudgetFound found
  have permitted :
      route = .frontier ∨ route = .obligation ∨ route = .activation ∨
        route = .direction ∨ route = .descent := by
    cases route <;> simp_all
  exact ⟨handle, route, found, failure, notColour, notCharge, notRank,
    notExactRoute, notBudget, permitted, descentMeaning⟩

/-- Named milestone endpoint for the checked Packet budget/HB activity edge. -/
theorem terminalBN6_packet_budget_hb_activity_bound_first_route_failure
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (bindingAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).checkPacketBudgetHBActivityBinding = true)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      ∃ route : TerminalPacketSelectorFaithfulnessRoute,
        family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
            table.environment.rankOf beforeRank afterRank handle = some route ∧
          family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
            table.environment.rankOf beforeRank afterRank handle route ∧
          route ≠ .colour ∧
          route ≠ .charge ∧
          route ≠ .rank ∧
          route ≠ .exactRoute ∧
          route ≠ .budget ∧
          (route = .frontier ∨ route = .obligation ∨ route = .activation ∨
            route = .direction ∨ route = .descent) ∧
          (route ≠ .descent ∨
            ¬(afterRank handle).LexLT (beforeRank handle)) :=
  conclusion.existsBudgetHBBoundFirstRouteFailure_of_selectorSilence table
    dependencyTable beforeRank afterRank bindingAccepted silenceAccepted
      closureAccepted

end DirectWire
end PNP
