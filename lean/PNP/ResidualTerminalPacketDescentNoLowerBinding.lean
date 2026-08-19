/-
Copyright (c) 2026 PNP Labs.

Checked local no-lower binding for the Packet descent route.  The checker
enumerates every canonical selector handle in an arbitrary finite grouped BN6
family and accepts exactly when no handle's fully computed Packet first route
is residual nondecrease (`.descent`).

The preceding checked semantic/HN and budget/HB bindings, selector silence,
and no-outcome HB closure force a positive Packet conclusion to expose such a
`.descent` route.  Consequently this local no-lower checker rejects, and an
assumed accepted row is contradictory under those explicit premises.

This is one executable local row toward the pinned manuscript's no-lower
ledger.  It does not construct terminal data or the complete ledger, cover
HResolve, BudgetResolve, normalization, saturation, replay, or named descent
routes, establish unconditional HB or ZeroSlack closure, prove PCCMin or
polynomial runtime, remove a project assumption, prove SAT in P, or prove
P = NP.
-/

import PNP.ResidualTerminalPacketSemanticHNActivityBinding

namespace PNP
namespace DirectWire

variable {Anchor ActivationAtom SemanticSignature TransportType Frontier
  ChargeOwner Obligation OriginKernel ModeProjection Direction Budget : Type}
variable [DecidableEq Anchor] [DecidableEq ActivationAtom]
  [DecidableEq Frontier] [DecidableEq Obligation] [DecidableEq Direction]
  [DecidableEq Budget]

/-! ## Exhaustive Packet descent no-lower row -/

/-- The local no-lower proposition for the fully computed Packet route: no
    canonical selector handle exposes residual nondecrease as its first failed
    route. -/
def TerminalBN6GroupedFamily.PacketDescentNoLower
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) : Prop :=
  ∀ handle : family.PacketSelectorHandle,
    family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
      rankOf beforeRank afterRank handle ≠ some .descent

/-- Exhaustively check the Packet descent no-lower row over every canonical
    selector handle. -/
def TerminalBN6GroupedFamily.checkPacketDescentNoLower
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) : Bool :=
  family.packetSelectorHandles.all fun handle =>
    decide
      (family.packetSelectorPayloadFirstRouteWithComputedBN5FrontierObligationActivationDirectionBudgetRoutes
        rankOf beforeRank afterRank handle ≠ some .descent)

/-- The Boolean scan recognizes exactly the all-handle Packet descent
    no-lower proposition. -/
theorem TerminalBN6GroupedFamily.checkPacketDescentNoLower_eq_true_iff
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget))
    (rankOf : family.PacketSelectorHandle → Fin rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) :
    family.checkPacketDescentNoLower rankOf beforeRank afterRank = true ↔
      family.PacketDescentNoLower rankOf beforeRank afterRank := by
  constructor
  · intro accepted handle
    have rowChecked := (List.all_eq_true.mp accepted) handle
      (family.mem_packetSelectorHandles handle)
    simpa only [decide_eq_true_eq] using rowChecked
  · intro noLower
    apply List.all_eq_true.mpr
    intro handle _handleMember
    simpa only [decide_eq_true_eq] using noLower handle

/-! ## Forced rejection at the checked Packet boundary -/

/-- A positive Packet conclusion plus the existing checked bindings and HB
    closure forces the exhaustive Packet descent no-lower checker to reject. -/
theorem TerminalBN6PacketConclusion.checkPacketDescentNoLower_eq_false_of_selectorSilence
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
    family.checkPacketDescentNoLower table.environment.rankOf
      beforeRank afterRank = false := by
  apply Bool.eq_false_iff.mpr
  intro noLowerAccepted
  have noLower :=
    (family.checkPacketDescentNoLower_eq_true_iff
      table.environment.rankOf beforeRank afterRank).1 noLowerAccepted
  obtain ⟨handle, found, _failure, _nondecreasing⟩ :=
    conclusion.existsSemanticHNBudgetBoundDescentFailure_of_selectorSilence
      table dependencyTable beforeRank afterRank semanticBindingAccepted
        budgetBindingAccepted silenceAccepted closureAccepted
  exact noLower handle found

/-- An accepted local Packet descent no-lower row contradicts the same checked
    positive-Packet premises. -/
theorem TerminalBN6PacketConclusion.false_of_checkedPacketDescentNoLower_and_selectorSilence
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
        beforeRank afterRank).environment = true)
    (noLowerAccepted : family.checkPacketDescentNoLower
      table.environment.rankOf beforeRank afterRank = true) : False := by
  have rejected :=
    conclusion.checkPacketDescentNoLower_eq_false_of_selectorSilence table
      dependencyTable beforeRank afterRank semanticBindingAccepted
        budgetBindingAccepted silenceAccepted closureAccepted
  rw [rejected] at noLowerAccepted
  cases noLowerAccepted

/-- Named milestone endpoint: the exhaustive local Packet descent no-lower row
    is rejected by the checked positive-Packet boundary. -/
theorem terminalBN6_packet_descent_no_lower_rejected
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
    family.checkPacketDescentNoLower table.environment.rankOf
      beforeRank afterRank = false :=
  conclusion.checkPacketDescentNoLower_eq_false_of_selectorSilence table
    dependencyTable beforeRank afterRank semanticBindingAccepted
      budgetBindingAccepted silenceAccepted closureAccepted

end DirectWire
end PNP
