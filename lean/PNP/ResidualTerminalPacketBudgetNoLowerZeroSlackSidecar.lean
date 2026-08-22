/-
Copyright (c) 2026 PNP Labs.

Proof-bearing Packet/budget no-lower sidecar for the report-facing ZeroSlack
certificate. The direct-wire candidate, candidate-derived saturation model,
finite budget, grouped Packet family, typed-realizer table, dependency table,
and residual ranks are explicit data. Acceptance is not a caller flag: the
existing same-candidate composition must recompute both finite ledgers and
return `true`.

The reflected result makes every governed budget-feasible support semantic
minimum, excludes every governed budget-feasible strict equivalent gain, and
excludes a positive Packet conclusion for the supplied family. The caps,
Packet payloads, ranks, realizer claims, activity environment, dependency
rows, and residual-rank maps remain inputs. This is the existing finite
two-branch boundary, not the manuscript's complete no-lower ledger. It does
not cover normalization, HResolve, saturation-loss, named-route, or replay
rows; construct terminal data; prove Packet adequacy; establish unconditional
ZeroSlack or PCCMin; prove polynomial runtime; put SAT in P; or prove P = NP.
-/

import PNP.ResidualTerminalPacketBudgetNoLowerComposition

namespace PNP

/-- Checked, proof-bearing Packet/budget no-lower evidence consumed by the
    structured ZeroSlack boundary. The single stored proposition is the exact
    equation returned by the executable same-candidate composition. -/
structure PacketBudgetNoLowerZeroSlackSidecarCertificate where
  Anchor : Type
  ActivationAtom : Type
  SemanticSignature : Type
  TransportType : Type
  Frontier : Type
  ChargeOwner : Type
  Obligation : Type
  OriginKernel : Type
  ModeProjection : Type
  Direction : Type
  PacketBudget : Type
  anchorDecidableEq : DecidableEq Anchor
  activationAtomDecidableEq : DecidableEq ActivationAtom
  frontierDecidableEq : DecidableEq Frontier
  obligationDecidableEq : DecidableEq Obligation
  directionDecidableEq : DecidableEq Direction
  packetBudgetDecidableEq : DecidableEq PacketBudget
  inputs : Nat
  gates : Nat
  outputs : Nat
  profileWidth : Nat
  rankCount : Nat
  budget : DirectWire.TerminalSupportBudget
  candidate : DirectWire.Candidate inputs gates outputs
  model : DirectWire.TerminalCandidateSaturationModel
    (profileWidth := profileWidth) candidate
  family : DirectWire.TerminalBN6GroupedFamily Anchor
    (DirectWire.TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
      SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection Direction PacketBudget)
  table : @DirectWire.TerminalPacketTypedRealizerTable
    Anchor
    (DirectWire.TerminalPacketSelectorBN5BudgetPayload rankCount ActivationAtom
      SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection Direction PacketBudget)
    anchorDecidableEq inputs outputs candidate.toImplementation family rankCount
  dependencyTable : DirectWire.TerminalPacketHBDependencyTable rankCount
  beforeRank : family.PacketSelectorHandle → DirectWire.TerminalResidualRank
  afterRank : family.PacketSelectorHandle → DirectWire.TerminalResidualRank
  compositionAccepted :
    DirectWire.checkTerminalPacketBudgetNoLowerComposition budget candidate
      model table dependencyTable beforeRank afterRank = true

attribute [instance]
  PacketBudgetNoLowerZeroSlackSidecarCertificate.anchorDecidableEq
  PacketBudgetNoLowerZeroSlackSidecarCertificate.activationAtomDecidableEq
  PacketBudgetNoLowerZeroSlackSidecarCertificate.frontierDecidableEq
  PacketBudgetNoLowerZeroSlackSidecarCertificate.obligationDecidableEq
  PacketBudgetNoLowerZeroSlackSidecarCertificate.directionDecidableEq
  PacketBudgetNoLowerZeroSlackSidecarCertificate.packetBudgetDecidableEq

/-- The stored Boolean equation exposes exactly the two finite ledger
    propositions recognized by the existing composed checker. -/
theorem PacketBudgetNoLowerZeroSlackSidecarCertificate.accepted
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :
    DirectWire.TerminalPacketBudgetNoLowerAccepted certificate.budget
      certificate.candidate certificate.model certificate.table
      certificate.dependencyTable certificate.beforeRank
      certificate.afterRank := by
  exact (DirectWire.checkTerminalPacketBudgetNoLowerComposition_eq_true_iff
    certificate.budget certificate.candidate certificate.model
      certificate.table certificate.dependencyTable certificate.beforeRank
      certificate.afterRank).mp certificate.compositionAccepted

/-- Every governed support admitted by the supplied finite budget is semantic
    minimum for the candidate-derived implementation. -/
theorem PacketBudgetNoLowerZeroSlackSidecarCertificate.all_feasible_support_minimum
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :
    ∀ seed,
      seed ∈ DirectWire.allTerminalSupportSeeds certificate.inputs
        certificate.gates certificate.outputs certificate.profileWidth →
      certificate.budget.Fits certificate.candidate certificate.model seed →
      DirectWire.IsSemanticallyMinimum
        (DirectWire.terminalHResolveSupportImplementation
          certificate.candidate certificate.model seed) :=
  (DirectWire.terminal_packet_budget_no_lower_composition_excludes_gain_and_packet
    certificate.budget certificate.candidate certificate.model
      certificate.table certificate.dependencyTable certificate.beforeRank
      certificate.afterRank certificate.compositionAccepted).1

/-- No governed budget-feasible support has a strict equivalent gain. -/
theorem PacketBudgetNoLowerZeroSlackSidecarCertificate.no_feasible_gain
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :
    ¬∃ seed,
      seed ∈ DirectWire.allTerminalSupportSeeds certificate.inputs
        certificate.gates certificate.outputs certificate.profileWidth ∧
      certificate.budget.Fits certificate.candidate certificate.model seed ∧
      ∃ next, DirectWire.StrictEquivalentGain
        (DirectWire.terminalHResolveSupportImplementation
          certificate.candidate certificate.model seed) next :=
  (DirectWire.terminal_packet_budget_no_lower_composition_excludes_gain_and_packet
    certificate.budget certificate.candidate certificate.model
      certificate.table certificate.dependencyTable certificate.beforeRank
      certificate.afterRank certificate.compositionAccepted).2.1

/-- The same checked composition excludes a positive Packet conclusion for
    the supplied grouped family. -/
theorem PacketBudgetNoLowerZeroSlackSidecarCertificate.no_positive_packet
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :
    ¬DirectWire.TerminalBN6PacketConclusion certificate.family :=
  (DirectWire.terminal_packet_budget_no_lower_composition_excludes_gain_and_packet
    certificate.budget certificate.candidate certificate.model
      certificate.table certificate.dependencyTable certificate.beforeRank
      certificate.afterRank certificate.compositionAccepted).2.2

/-- Named M180 endpoint: one proof-bearing sidecar retains exactly the current
    finite Packet/budget no-lower consequences through the ZeroSlack boundary. -/
theorem packet_budget_no_lower_zeroslack_sidecar_checked_complete
    (certificate : PacketBudgetNoLowerZeroSlackSidecarCertificate) :
    (∀ seed,
      seed ∈ DirectWire.allTerminalSupportSeeds certificate.inputs
        certificate.gates certificate.outputs certificate.profileWidth →
      certificate.budget.Fits certificate.candidate certificate.model seed →
      DirectWire.IsSemanticallyMinimum
        (DirectWire.terminalHResolveSupportImplementation
          certificate.candidate certificate.model seed)) ∧
    (¬∃ seed,
      seed ∈ DirectWire.allTerminalSupportSeeds certificate.inputs
        certificate.gates certificate.outputs certificate.profileWidth ∧
      certificate.budget.Fits certificate.candidate certificate.model seed ∧
      ∃ next, DirectWire.StrictEquivalentGain
        (DirectWire.terminalHResolveSupportImplementation
          certificate.candidate certificate.model seed) next) ∧
    ¬DirectWire.TerminalBN6PacketConclusion certificate.family := by
  exact ⟨certificate.all_feasible_support_minimum,
    certificate.no_feasible_gain, certificate.no_positive_packet⟩

end PNP
