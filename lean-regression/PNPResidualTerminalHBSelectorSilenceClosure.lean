import PNP.ResidualTerminalHBSelectorSilenceClosure

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

/-! ## Arbitrary finite selector-rank closure -/

variable {Atom Payload : Type} [DecidableEq Atom]
variable {inputs outputs rankCount : Nat}
variable {current : Implementation inputs outputs}
variable {family : TerminalBN6GroupedFamily Atom Payload}

/-- The central theorem is polymorphic in the grouped family, selector count,
    direct-wire arities, rank count, and all supplied executable tables. -/
example
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (realizerAccepted : realizerTable.checkFaithful = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (noGain : ∀ next : Implementation inputs outputs,
      ¬StrictEquivalentGain current next) :
    ∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false :=
  realizerTable.noFaithful_of_noStrictEquivalentGain dependencyTable
    realizerAccepted closureAccepted noGain

/-- The complete canonical contract retains selector silence, checked
    dependency validity, HN/BUD silence, and well-foundedness together. -/
example
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (realizerAccepted : realizerTable.checkFaithful = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (noGain : ∀ next : Implementation inputs outputs,
      ¬StrictEquivalentGain current next) :
    (∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false) ∧
      dependencyTable.NoOutcomeActiveClosureValid realizerTable.environment ∧
      (∀ node, realizerTable.environment.hbActive node = false) ∧
      WellFounded dependencyTable.Depends :=
  terminalBN6_packet_typed_realizer_hb_selector_silence_closure_contract
    realizerTable dependencyTable realizerAccepted closureAccepted noGain

/-! ## Explicit gain-coverage specialization -/

variable {CandidateAtom : Type} [DecidableEq CandidateAtom]
variable {candidateFamily : TerminalBN6GroupedFamily CandidateAtom
  (Implementation inputs outputs)}

/-- Exact source-cell no-gain plus the explicit global coverage certificate
    supplies the semantic premise used by the rank induction. -/
example
    (realizerTable : TerminalPacketTypedRealizerTable
      current candidateFamily rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (realizerAccepted : realizerTable.checkFaithful = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (coverage : TerminalPacketSelectorGainCoverage candidateFamily current)
    (sourceNoGain : ∀ handle : candidateFamily.PacketSelectorHandle,
      ∀ atom, atom ∈ (candidateFamily.packetSelectorCell handle).atoms →
        ¬StrictEquivalentGain current atom.payload) :
    ∀ handle : candidateFamily.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false :=
  realizerTable.noFaithful_of_gainCoverageNoGain dependencyTable
    realizerAccepted closureAccepted coverage sourceNoGain

example
    (realizerTable : TerminalPacketTypedRealizerTable
      current candidateFamily rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (realizerAccepted : realizerTable.checkFaithful = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (coverage : TerminalPacketSelectorGainCoverage candidateFamily current)
    (sourceNoGain : ∀ handle : candidateFamily.PacketSelectorHandle,
      ∀ atom, atom ∈ (candidateFamily.packetSelectorCell handle).atoms →
        ¬StrictEquivalentGain current atom.payload) :
    (∀ handle : candidateFamily.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false) ∧
      dependencyTable.NoOutcomeActiveClosureValid realizerTable.environment ∧
      (∀ node, realizerTable.environment.hbActive node = false) ∧
      WellFounded dependencyTable.Depends :=
  terminalBN6_packet_typed_realizer_hb_selector_silence_gain_coverage_contract
    realizerTable dependencyTable realizerAccepted closureAccepted coverage
      sourceNoGain

end DirectWire
end PNP
