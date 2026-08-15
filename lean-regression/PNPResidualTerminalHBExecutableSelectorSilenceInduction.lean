import PNP.ResidualTerminalHBExecutableSelectorSilenceInduction

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

variable {Atom Payload : Type} [DecidableEq Atom]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {family : TerminalBN6GroupedFamily Atom Payload}

/-! ## Exact executable selector silence -/

/-- The all-row checker exposes both faithful-row validity and an exact bottom
    equation for every canonical handle. -/
example
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (accepted : table.checkSelectorSilent = true) :
    table.checkFaithful = true ∧
      ∀ handle : family.PacketSelectorHandle,
        ∃ reason : TerminalPacketTypedRealizerBot
            family.PacketSelectorHandle rankCount,
          table.claim handle = .bot reason :=
  (table.checkSelectorSilent_eq_true_iff).mp accepted

/-- A gain constructor cannot be hidden inside an accepted selector-silence
    table, even when the blueprint itself might pass its validator. -/
example
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (handle : family.PacketSelectorHandle)
    (blueprint : TerminalPacketUnitChargeBlueprint current)
    (claimEquation : table.claim handle = .gain blueprint) :
    table.checkSelectorSilent = false := by
  cases checked : table.checkSelectorSilent with
  | false => rfl
  | true =>
      obtain ⟨reason, botEquation⟩ :=
        table.claim_eq_bot_of_selectorSilent checked handle
      rw [claimEquation] at botEquation
      cases botEquation

/-! ## Arbitrary finite-rank induction -/

/-- The central theorem has no global semantic no-gain or gain-coverage
    premise. -/
example
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (silenceAccepted : realizerTable.checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true) :
    ∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false :=
  realizerTable.noFaithful_of_selectorSilent dependencyTable
    silenceAccepted closureAccepted

/-- Explicit manuscript form at every supplied finite rank. -/
example
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (silenceAccepted : realizerTable.checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (rank : Fin rankCount) :
    ∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.rankOf handle ≤ rank →
        realizerTable.environment.faithful handle = false :=
  realizerTable.noFaithfulAtOrBelow_of_selectorSilent dependencyTable
    silenceAccepted closureAccepted rank

/-- The complete canonical contract retains selector silence, exact bottom
    rows, checked HB validity and inactivity, and well-foundedness together. -/
example
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (silenceAccepted : realizerTable.checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true) :
    (∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false) ∧
      (∀ handle : family.PacketSelectorHandle,
        ∃ reason : TerminalPacketTypedRealizerBot
            family.PacketSelectorHandle rankCount,
          realizerTable.claim handle = .bot reason) ∧
      dependencyTable.NoOutcomeActiveClosureValid realizerTable.environment ∧
      (∀ node, realizerTable.environment.hbActive node = false) ∧
      WellFounded dependencyTable.Depends :=
  terminalBN6_packet_typed_realizer_hb_selector_silence_induction_contract
    realizerTable dependencyTable silenceAccepted closureAccepted

end DirectWire
end PNP
