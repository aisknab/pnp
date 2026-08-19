/-
Copyright (c) 2026 PNP Labs.

Checked binding from the four remaining exact Packet semantic mismatches to
the existing HB hereditary-normalization activity table.  The checker
enumerates every canonical selector handle in an arbitrary finite grouped BN6
family.  At each handle it requires either simultaneous frontier, obligation,
activation, and direction equality or activity of the HN node at the table's
authoritative handle rank.

The already proved no-outcome HB closure forces every supplied HN/BUD activity
bit false.  Composing that closure with the checked semantic binding therefore
proves all four equalities.  Together with the separately checked budget/HB
binding, the forced Packet first route is exactly residual nondecrease.

The typed coordinates and directions, grouped family, rank map, activity
table, dependency rows, residual ranks, realizer claims, and both checked
bindings remain explicit inputs.  This module does not construct those data
from terminal input, prove HN or blocker semantic completeness, derive the HB
tables, establish a decreasing transition, close unconditional HB negative
closure, prove ZeroSlack, PCCMin, polynomial runtime, SAT in P, remove a
project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalPacketBudgetHBActivityBinding

namespace PNP
namespace DirectWire

variable {Anchor ActivationAtom SemanticSignature TransportType Frontier
  ChargeOwner Obligation OriginKernel ModeProjection Direction Budget : Type}
variable [DecidableEq Anchor]

/-! ## Exact remaining semantic agreement -/

/-- Simultaneous agreement of the four exact non-budget semantic fields still
    exposed by the budget/HB-bound Packet endpoint. -/
def TerminalPacketTypedRealizerTable.PacketSemanticFieldsAgree
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (_table : TerminalPacketTypedRealizerTable current family rankCount)
    (handle : family.PacketSelectorHandle) : Prop :=
  let payload := (family.packetSelectorPayloadAtom handle).payload
  payload.checks.checks.sourceCoordinate.frontier =
      payload.checks.checks.selectorCoordinate.frontier ∧
    payload.checks.checks.sourceCoordinate.obligation =
      payload.checks.checks.selectorCoordinate.obligation ∧
    payload.checks.checks.sourceCoordinate.key.atom =
      payload.checks.checks.selectorCoordinate.key.atom ∧
    payload.checks.sourceDirection = payload.checks.selectorDirection

/-- Exact proposition checked at the local Packet/HB boundary: any failure of
    the four remaining semantic equalities activates the HN node at the
    handle's authoritative finite rank. -/
def TerminalPacketTypedRealizerTable.PacketSemanticHNActivityBound
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount) : Prop :=
  ∀ handle : family.PacketSelectorHandle,
    ¬table.PacketSemanticFieldsAgree handle →
      table.environment.hnActive (table.environment.rankOf handle) = true

variable [DecidableEq ActivationAtom] [DecidableEq Frontier]
  [DecidableEq Obligation] [DecidableEq Direction]

/-- Exhaustively check simultaneous semantic agreement or authoritative-rank
    HN activity for every canonical handle. -/
def TerminalPacketTypedRealizerTable.checkPacketSemanticHNActivityBinding
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount) : Bool :=
  family.packetSelectorHandles.all fun handle =>
    let payload := (family.packetSelectorPayloadAtom handle).payload
    (decide (payload.checks.checks.sourceCoordinate.frontier =
          payload.checks.checks.selectorCoordinate.frontier) &&
        (decide (payload.checks.checks.sourceCoordinate.obligation =
            payload.checks.checks.selectorCoordinate.obligation) &&
          (decide (payload.checks.checks.sourceCoordinate.key.atom =
              payload.checks.checks.selectorCoordinate.key.atom) &&
            decide (payload.checks.sourceDirection =
              payload.checks.selectorDirection)))) ||
      table.environment.hnActive (table.environment.rankOf handle)

/-- The Boolean scan recognizes exactly the all-handle Packet-to-HN semantic
    activity proposition. -/
theorem TerminalPacketTypedRealizerTable.checkPacketSemanticHNActivityBinding_eq_true_iff
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount) :
    table.checkPacketSemanticHNActivityBinding = true ↔
      table.PacketSemanticHNActivityBound := by
  constructor
  · intro accepted handle mismatch
    have rowChecked := (List.all_eq_true.mp accepted) handle
      (family.mem_packetSelectorHandles handle)
    have alternatives :
        table.PacketSemanticFieldsAgree handle ∨
          table.environment.hnActive
            (table.environment.rankOf handle) = true := by
      simpa only [TerminalPacketTypedRealizerTable.PacketSemanticFieldsAgree,
        Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using rowChecked
    exact alternatives.resolve_left mismatch
  · intro bound
    apply List.all_eq_true.mpr
    intro handle _handleMember
    letI : Decidable (table.PacketSemanticFieldsAgree handle) := by
      unfold TerminalPacketTypedRealizerTable.PacketSemanticFieldsAgree
      infer_instance
    have alternatives :
        table.PacketSemanticFieldsAgree handle ∨
          table.environment.hnActive
            (table.environment.rankOf handle) = true := by
      by_cases agree : table.PacketSemanticFieldsAgree handle
      · exact Or.inl agree
      · exact Or.inr (bound handle agree)
    simpa only [TerminalPacketTypedRealizerTable.PacketSemanticFieldsAgree,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using alternatives

/-! ## Checked HB closure consequences -/

/-- Checked semantic binding plus checked well-founded HB no-outcome closure
    forces all four remaining typed semantic fields to agree. -/
theorem TerminalPacketTypedRealizerTable.packetSemanticFieldsAgree_of_checkedHNActivityBinding
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (bindingAccepted : table.checkPacketSemanticHNActivityBinding = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      table.environment = true)
    (handle : family.PacketSelectorHandle) :
    table.PacketSemanticFieldsAgree handle := by
  letI : Decidable (table.PacketSemanticFieldsAgree handle) := by
    unfold TerminalPacketTypedRealizerTable.PacketSemanticFieldsAgree
    infer_instance
  by_cases agree : table.PacketSemanticFieldsAgree handle
  · exact agree
  · have bound :=
      (table.checkPacketSemanticHNActivityBinding_eq_true_iff).1 bindingAccepted
    have active := bound handle agree
    have inactive := dependencyTable.hnActive_eq_false table.environment
      closureAccepted (table.environment.rankOf handle)
    rw [inactive] at active
    cases active

variable [DecidableEq Budget]

/-- Consequently none of the four remaining semantic first routes can occur
    after the checked Packet/HN binding and HB closure have passed. -/
theorem TerminalPacketTypedRealizerTable.packetSelectorSemanticFirstRoutes_ne_of_checkedHNActivityBinding
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
    (bindingAccepted : table.checkPacketSemanticHNActivityBinding = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      table.environment = true)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        table.environment.rankOf beforeRank afterRank handle ≠ some .frontier ∧
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        table.environment.rankOf beforeRank afterRank handle ≠ some .obligation ∧
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        table.environment.rankOf beforeRank afterRank handle ≠ some .activation ∧
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        table.environment.rankOf beforeRank afterRank handle ≠ some .direction := by
  have agreement := table.packetSemanticFieldsAgree_of_checkedHNActivityBinding
    dependencyTable bindingAccepted closureAccepted handle
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro found
    have mismatch :=
      (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_frontier_iff
        table.environment.rankOf beforeRank afterRank handle).1 found
    exact mismatch agreement.1
  · intro found
    have mismatch :=
      (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_obligation_iff
        table.environment.rankOf beforeRank afterRank handle).1 found
    exact mismatch.2 agreement.2.1
  · intro found
    have mismatch :=
      (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_activation_iff
        table.environment.rankOf beforeRank afterRank handle).1 found
    exact mismatch.2.2 agreement.2.2.1
  · intro found
    have mismatch :=
      (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes_eq_some_direction_iff
        table.environment.rankOf beforeRank afterRank handle).1 found
    exact mismatch.2.2.2 agreement.2.2.2

/-! ## Positive-Packet endpoint reduced to residual nondecrease -/

/-- Executable selector silence, checked HB closure, the semantic/HN binding,
    and the budget/HB binding force the sole remaining exact first route:
    residual nondecrease. -/
theorem TerminalBN6PacketConclusion.existsSemanticHNBudgetBoundDescentFailure_of_selectorSilence
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
    (semanticBindingAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).checkPacketSemanticHNActivityBinding = true)
    (budgetBindingAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).checkPacketBudgetHBActivityBinding = true)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
          table.environment.rankOf beforeRank afterRank handle = some .descent ∧
        family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
          table.environment.rankOf beforeRank afterRank handle .descent ∧
        ¬(afterRank handle).LexLT (beforeRank handle) := by
  obtain ⟨handle, route, found, failure, _notColour, _notCharge, _notRank,
      _notExactRoute, notBudget, permitted, descentMeaning⟩ :=
    conclusion.existsBudgetHBBoundFirstRouteFailure_of_selectorSilence table
      dependencyTable beforeRank afterRank budgetBindingAccepted
        silenceAccepted closureAccepted
  change table.checkPacketSemanticHNActivityBinding = true at semanticBindingAccepted
  change dependencyTable.checkNoOutcomeActiveClosure table.environment = true at closureAccepted
  have semanticRoutes :=
    table.packetSelectorSemanticFirstRoutes_ne_of_checkedHNActivityBinding
      dependencyTable beforeRank afterRank semanticBindingAccepted
        closureAccepted handle
  have routeDescent : route = .descent := by
    rcases permitted with frontier | obligation | activation | direction | descent
    · subst route
      exact (semanticRoutes.1 found).elim
    · subst route
      exact (semanticRoutes.2.1 found).elim
    · subst route
      exact (semanticRoutes.2.2.1 found).elim
    · subst route
      exact (semanticRoutes.2.2.2 found).elim
    · exact descent
  subst route
  have nondecreasing : ¬(afterRank handle).LexLT (beforeRank handle) := by
    simpa using descentMeaning
  exact ⟨handle, found, failure, nondecreasing⟩

/-- Named milestone endpoint for the checked Packet semantic/HN activity
    edge, composed with the separately checked budget/HB edge. -/
theorem terminalBN6_packet_semantic_hn_activity_bound_descent_failure
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
    (semanticBindingAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).checkPacketSemanticHNActivityBinding = true)
    (budgetBindingAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).checkPacketBudgetHBActivityBinding = true)
    (silenceAccepted :
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      (table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
        beforeRank afterRank).environment = true) :
    ∃ handle : family.PacketSelectorHandle,
      family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
          table.environment.rankOf beforeRank afterRank handle = some .descent ∧
        family.packetSelectorPayloadFailureAtWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
          table.environment.rankOf beforeRank afterRank handle .descent ∧
        ¬(afterRank handle).LexLT (beforeRank handle) :=
  conclusion.existsSemanticHNBudgetBoundDescentFailure_of_selectorSilence table
    dependencyTable beforeRank afterRank semanticBindingAccepted
      budgetBindingAccepted silenceAccepted closureAccepted

end DirectWire
end PNP
