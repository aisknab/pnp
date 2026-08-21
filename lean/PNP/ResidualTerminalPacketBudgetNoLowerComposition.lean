/-
Copyright (c) 2026 PNP Labs.

Executable composition of two independently checked finite branches of the
pinned manuscript's no-lower ledger.  One Boolean evaluates the complete
canonical terminal budget-support ledger and the checked Packet ledger over
the same direct-wire candidate.

Acceptance proves that every budget-feasible canonical support is a semantic
minimum, excludes every such support's strict equivalent gain, and excludes a
positive Packet conclusion for the supplied grouped family and tables.

The budget caps, Packet family, typed payloads, ranks, realizer claims,
activity environment, and dependency rows remain supplied.  This is a finite
two-branch composition, not the manuscript's complete no-lower ledger.  It
does not construct HN/BUD grammar or Packet data from terminal data, implement
polynomial HResolve or BudgetResolve, cover normalization, saturation, replay,
or remaining named routes, establish unconditional ZeroSlack, prove PCCMin or
polynomial runtime, remove a project assumption, prove SAT in P, or prove
P = NP.
-/

import PNP.ResidualTerminalPacketNoLowerLedger
import PNP.ResidualTerminalBudgetNoLowerLedger

namespace PNP
namespace DirectWire

variable {Anchor ActivationAtom SemanticSignature TransportType Frontier
  ChargeOwner Obligation OriginKernel ModeProjection Direction
  PacketBudget : Type}
variable [DecidableEq Anchor] [DecidableEq ActivationAtom]
  [DecidableEq Frontier] [DecidableEq Obligation] [DecidableEq Direction]
  [DecidableEq PacketBudget]

/-! ## Joint executable boundary -/

/-- Exact semantic proposition recognized by the composed checker.  Both
    component propositions are independently reflected from their component
    Booleans; there is no caller-supplied composition-success bit. -/
def TerminalPacketBudgetNoLowerAccepted
    {inputs gates outputs profileWidth rankCount : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction PacketBudget)}
    (table : TerminalPacketTypedRealizerTable
      candidate.toImplementation family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) : Prop :=
  TerminalBudgetNoLowerLedgerAccepted budget candidate model ∧
    table.PacketNoLowerLedgerAccepted dependencyTable beforeRank afterRank

/-- Recompute both finite no-lower branches over one candidate and accept only
    when both component ledgers accept. -/
def checkTerminalPacketBudgetNoLowerComposition
    {inputs gates outputs profileWidth rankCount : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction PacketBudget)}
    (table : TerminalPacketTypedRealizerTable
      candidate.toImplementation family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) : Bool :=
  checkTerminalBudgetNoLowerLedger budget candidate model &&
    table.checkPacketNoLowerLedger dependencyTable beforeRank afterRank

/-- The composed Boolean recognizes exactly the conjunction of the two
    independently checked finite ledger propositions. -/
theorem checkTerminalPacketBudgetNoLowerComposition_eq_true_iff
    {inputs gates outputs profileWidth rankCount : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction PacketBudget)}
    (table : TerminalPacketTypedRealizerTable
      candidate.toImplementation family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) :
    checkTerminalPacketBudgetNoLowerComposition budget candidate model table
        dependencyTable beforeRank afterRank = true ↔
      TerminalPacketBudgetNoLowerAccepted budget candidate model table
        dependencyTable beforeRank afterRank := by
  simp only [checkTerminalPacketBudgetNoLowerComposition,
    TerminalPacketBudgetNoLowerAccepted, Bool.and_eq_true]
  constructor
  · rintro ⟨budgetChecked, packetChecked⟩
    exact ⟨
      (checkTerminalBudgetNoLowerLedger_eq_true_iff
        budget candidate model).1 budgetChecked,
      (table.checkPacketNoLowerLedger_eq_true_iff dependencyTable
        beforeRank afterRank).1 packetChecked⟩
  · rintro ⟨budgetAccepted, packetAccepted⟩
    exact ⟨
      (checkTerminalBudgetNoLowerLedger_eq_true_iff
        budget candidate model).2 budgetAccepted,
      (table.checkPacketNoLowerLedger_eq_true_iff dependencyTable
        beforeRank afterRank).2 packetAccepted⟩

/-! ## Joint semantic result -/

/-- Named M173 endpoint: acceptance simultaneously exposes all feasible
    support minima, excludes a feasible strict-equivalent-gain witness, and
    excludes a positive Packet over the same candidate. -/
theorem terminal_packet_budget_no_lower_composition_excludes_gain_and_packet
    {inputs gates outputs profileWidth rankCount : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction PacketBudget)}
    (table : TerminalPacketTypedRealizerTable
      candidate.toImplementation family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    (accepted : checkTerminalPacketBudgetNoLowerComposition budget candidate
      model table dependencyTable beforeRank afterRank = true) :
    (∀ seed,
      seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth →
      budget.Fits candidate model seed →
      IsSemanticallyMinimum
        (terminalHResolveSupportImplementation candidate model seed)) ∧
    (¬∃ seed,
      seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ∧
      budget.Fits candidate model seed ∧
      ∃ next, StrictEquivalentGain
        (terminalHResolveSupportImplementation candidate model seed) next) ∧
    ¬TerminalBN6PacketConclusion family := by
  have componentAccepted :=
    (checkTerminalPacketBudgetNoLowerComposition_eq_true_iff budget candidate
      model table dependencyTable beforeRank afterRank).1 accepted
  have budgetChecked :=
    (checkTerminalBudgetNoLowerLedger_eq_true_iff
      budget candidate model).2 componentAccepted.1
  have packetChecked :=
    (table.checkPacketNoLowerLedger_eq_true_iff dependencyTable
      beforeRank afterRank).2 componentAccepted.2
  have budgetResult :=
    terminal_budget_no_lower_ledger_excludes_feasible_gain
      budget candidate model budgetChecked
  have packetResult :=
    terminalBN6_packet_no_lower_ledger_excludes_positive_packet table
      dependencyTable beforeRank afterRank packetChecked
  exact ⟨budgetResult.1, budgetResult.2, packetResult⟩

/-- A governed feasible gain forces the composed checker to reject. -/
theorem checkTerminalPacketBudgetNoLowerComposition_eq_false_of_feasible_gain
    {inputs gates outputs profileWidth rankCount : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction PacketBudget)}
    (table : TerminalPacketTypedRealizerTable
      candidate.toImplementation family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank)
    {seed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)}
    (governed : seed ∈ allTerminalSupportSeeds
      inputs gates outputs profileWidth)
    (fits : budget.Fits candidate model seed)
    (gain : ∃ next, StrictEquivalentGain
      (terminalHResolveSupportImplementation candidate model seed) next) :
    checkTerminalPacketBudgetNoLowerComposition budget candidate model table
      dependencyTable beforeRank afterRank = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have result :=
    terminal_packet_budget_no_lower_composition_excludes_gain_and_packet
      budget candidate model table dependencyTable beforeRank afterRank accepted
  exact result.2.1 ⟨seed, governed, fits, gain⟩

/-- A positive Packet forces the composed checker to reject. -/
theorem TerminalBN6PacketConclusion.checkTerminalPacketBudgetNoLowerComposition_eq_false
    {inputs gates outputs profileWidth rankCount : Nat}
    (budget : TerminalSupportBudget)
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    {family : TerminalBN6GroupedFamily Anchor
      (TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
        SemanticSignature TransportType Frontier ChargeOwner Obligation
        OriginKernel ModeProjection Direction PacketBudget)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable
      candidate.toImplementation family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (beforeRank afterRank : family.PacketSelectorHandle →
      TerminalResidualRank) :
    checkTerminalPacketBudgetNoLowerComposition budget candidate model table
      dependencyTable beforeRank afterRank = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have result :=
    terminal_packet_budget_no_lower_composition_excludes_gain_and_packet
      budget candidate model table dependencyTable beforeRank afterRank accepted
  exact result.2.2 conclusion

end DirectWire
end PNP
