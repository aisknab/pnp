/-
Copyright (c) 2026 PNP Labs.

Executable composition of the checked Packet branch of the pinned manuscript's
no-lower ledger.  One Boolean evaluates the semantic/HN binding, budget/HB
binding, selector-silence, HB no-outcome closure, and exhaustive Packet
descent/no-lower row for the same supplied finite family and tables.

M167 proves that a positive Packet forces the final row to reject when the
first four checks accept.  Consequently the composite ledger rejects every
positive Packet, and ledger acceptance proves that no positive Packet
conclusion exists for those exact inputs.

This closes only the Packet branch of the no-lower ledger over supplied data.
It does not construct terminal data or the complete ledger, implement HResolve,
BudgetResolve, normalization, saturation, replay, or other named routes,
establish unconditional HB or ZeroSlack closure, prove PCCMin or polynomial
runtime, remove a project assumption, prove SAT in P, or prove P = NP.
-/

import PNP.ResidualTerminalPacketDescentNoLowerBinding

namespace PNP
namespace DirectWire

variable {Anchor ActivationAtom SemanticSignature TransportType Frontier
  ChargeOwner Obligation OriginKernel ModeProjection Direction Budget : Type}
variable [DecidableEq Anchor] [DecidableEq ActivationAtom]
  [DecidableEq Frontier] [DecidableEq Obligation] [DecidableEq Direction]
  [DecidableEq Budget]

/-! ## Executable Packet no-lower ledger -/

/-- The exact five checked rows that constitute the current Packet branch of
    the no-lower ledger.  Every field is an equation produced by an executable
    checker over the same supplied family, table, dependency table, and ranks. -/
def TerminalPacketTypedRealizerTable.PacketNoLowerLedgerAccepted
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) : Prop :=
  let computed :=
    table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
      beforeRank afterRank
  computed.checkPacketSemanticHNActivityBinding = true ∧
    computed.checkPacketBudgetHBActivityBinding = true ∧
    computed.checkSelectorSilent = true ∧
    dependencyTable.checkNoOutcomeActiveClosure computed.environment = true ∧
    family.checkPacketDescentNoLower table.environment.rankOf
      beforeRank afterRank = true

/-- Evaluate the complete current Packet ledger boundary.  There is no
    caller-supplied ledger-success bit: all five rows are recomputed. -/
def TerminalPacketTypedRealizerTable.checkPacketNoLowerLedger
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) : Bool :=
  let computed :=
    table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness
      beforeRank afterRank
  computed.checkPacketSemanticHNActivityBinding &&
    computed.checkPacketBudgetHBActivityBinding &&
    computed.checkSelectorSilent &&
    dependencyTable.checkNoOutcomeActiveClosure computed.environment &&
    family.checkPacketDescentNoLower table.environment.rankOf
      beforeRank afterRank

/-- The composite Boolean recognizes exactly the five checked Packet ledger
    rows. -/
theorem TerminalPacketTypedRealizerTable.checkPacketNoLowerLedger_eq_true_iff
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction Budget)}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) :
    table.checkPacketNoLowerLedger dependencyTable beforeRank afterRank = true ↔
      table.PacketNoLowerLedgerAccepted dependencyTable beforeRank afterRank := by
  simp only [TerminalPacketTypedRealizerTable.checkPacketNoLowerLedger,
    TerminalPacketTypedRealizerTable.PacketNoLowerLedgerAccepted,
    Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨semantic, budget⟩, silence⟩, closure⟩, noLower⟩
    exact ⟨semantic, budget, silence, closure, noLower⟩
  · rintro ⟨semantic, budget, silence, closure, noLower⟩
    exact ⟨⟨⟨⟨semantic, budget⟩, silence⟩, closure⟩, noLower⟩

/-! ## Positive-Packet exclusion -/

/-- A positive Packet forces the exact composite Packet ledger to reject. -/
theorem TerminalBN6PacketConclusion.checkPacketNoLowerLedger_eq_false
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
      TerminalResidualRank) :
    table.checkPacketNoLowerLedger dependencyTable beforeRank afterRank = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  rcases (table.checkPacketNoLowerLedger_eq_true_iff dependencyTable
    beforeRank afterRank).1 accepted with
    ⟨semanticBindingAccepted, budgetBindingAccepted, silenceAccepted,
      closureAccepted, noLowerAccepted⟩
  exact conclusion.false_of_checkedPacketDescentNoLower_and_selectorSilence
    table dependencyTable beforeRank afterRank semanticBindingAccepted
      budgetBindingAccepted silenceAccepted closureAccepted noLowerAccepted

/-- An accepted composite ledger excludes a positive Packet conclusion for the
    same supplied family, table, dependency table, and residual ranks. -/
theorem TerminalPacketTypedRealizerTable.not_packetConclusion_of_checkedPacketNoLowerLedger
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
    (ledgerAccepted : table.checkPacketNoLowerLedger dependencyTable
      beforeRank afterRank = true) :
    ¬TerminalBN6PacketConclusion family := by
  intro conclusion
  have rejected := conclusion.checkPacketNoLowerLedger_eq_false table
    dependencyTable beforeRank afterRank
  rw [rejected] at ledgerAccepted
  cases ledgerAccepted

/-- Named milestone endpoint: acceptance of the executable Packet no-lower
    ledger rules out a positive Packet over the same arbitrary finite data. -/
theorem terminalBN6_packet_no_lower_ledger_excludes_positive_packet
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
    (ledgerAccepted : table.checkPacketNoLowerLedger dependencyTable
      beforeRank afterRank = true) :
    ¬TerminalBN6PacketConclusion family :=
  table.not_packetConclusion_of_checkedPacketNoLowerLedger dependencyTable
    beforeRank afterRank ledgerAccepted

end DirectWire
end PNP
